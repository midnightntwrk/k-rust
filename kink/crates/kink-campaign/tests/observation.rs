//! The observation slot (`RunOptions::observe`): a campaign over a definition that never ends
//! compares its runs by declared observation channels, and kills a mutant at the first decided
//! difference of a finite prefix (`testdata/k/console.k`, a free-running console whose `tick`
//! advances the count `<n>`, whose `emit` appends to the `<out>` log every third step, and whose
//! `<phase>` is bookkeeping).
//!
//! Every run of `run` is cut by the depth bound, so the baseline is a prefix program: its end
//! slots compare nothing, and each channel is compared up to its horizon. A front end's functions
//! of an observer give a class's contents and filter its events (`Halved`).

#[path = "../../../testdata/k/support.rs"]
mod support;

use std::collections::BTreeSet;
use std::path::Path;
use std::time::Duration;

use k_rust::definition::{AttributeKey, Attributes, Sentence};
use k_rust::kast::{Sort, Term};
use k_rust::kompile::CompileOptions;
use k_rust::kore::ast::Pattern;
use kink_campaign::{
    Campaign, CampaignFailureKind, CampaignOptions, CampaignRun, ChannelEnd, CrashPolicy, Element,
    Evaluated, Log, MutantScopeFailure, MutantStatus, Observation, ObservationEvaluator,
    ObservationFunctions, ObservationVerdict, Observe, ObserveFunctions, OracleDeclaration,
    OracleOutcome, PointClass, Position, Projection, RunOptions, ScheduleMode,
    SelectionPolicy as Sel, StateProjection, Stutter, TestCase, TestRun, WorkBudget,
    run_campaign_with,
};
use kink_native::NativeValidator;
use kink_native::execution::{ExecutionBudget, ProbeState};
use kink_patch::{
    Baseline, CandidateGeneration, Edit, InsertPosition, Patch, SelectionPolicy, SiteSelector,
    TermRef, derive_sites, select,
};
use kink_pattern::ExecutionTerminalKind;

fn normal(_: &Pattern) -> ExecutionTerminalKind {
    ExecutionTerminalKind::Normal
}

fn validator() -> NativeValidator {
    NativeValidator::bind(
        support::load_path(&Path::new(support::DIR).join("console.k"), "CONSOLE"),
        CompileOptions::default(),
    )
}

/// The configuration `<k> run </k> <n> count </n> <phase> 0 </phase> <out> .List </out>`.
fn console_from(count: i64) -> Pattern {
    let initial = support::initial_state(support::app("Lblrun", Vec::new()), "SortCmd");
    let Pattern::Application { symbol, arguments } = &initial else {
        unreachable!("a configuration is an application");
    };
    let cell = |name: &str, content: Pattern| {
        support::app(&format!("Lbl'-LT-'{name}'-GT-'"), vec![content])
    };
    let [k, counter] = [arguments[0].clone(), arguments[1].clone()];
    Pattern::Application {
        symbol: symbol.clone(),
        arguments: vec![
            k,
            cell("n", support::int(count)),
            cell("phase", support::int(0)),
            cell("out", support::app("Lbl'Stop'List", Vec::new())),
            counter,
        ],
    }
}

/// The configuration `console_from(0)` whose `<phase>` holds `phase` and whose `<out>` holds
/// `out`, each written in KORE.
fn console_holding(phase: &str, out: &str) -> Pattern {
    let initial = console_from(0);
    let Pattern::Application { symbol, arguments } = &initial else {
        unreachable!("a configuration is an application");
    };
    let cell = |name: &str, content: &str| {
        support::app(
            &format!("Lbl'-LT-'{name}'-GT-'"),
            vec![k_rust::kore::parser::parse_pattern(content).unwrap()],
        )
    };
    let mut arguments = arguments.clone();
    arguments[2] = cell("phase", phase);
    arguments[3] = cell("out", out);
    Pattern::Application {
        symbol: symbol.clone(),
        arguments,
    }
}

fn test(id: &str) -> TestCase {
    test_from(id, 0, CrashPolicy::Reject)
}

/// The test `id` from the count `count`, whose one whole-term slot declares `crashes`.
fn test_from(id: &str, count: i64, crashes: CrashPolicy) -> TestCase {
    TestCase {
        id: id.into(),
        initial_state: console_from(count),
        oracles: vec![
            OracleDeclaration::new(crashes, Projection::State(StateProjection::WholeTerm)).unwrap(),
        ],
    }
}

/// The time bound of every run: nextest stops a test after ten minutes, so this clock fires only
/// on a test that fails anyway, and the depth bound or the work budget decides every passing run.
const NO_CLOCK: Duration = Duration::from_secs(600);

/// Each path's depth bound: 24 steps are 16 ticks and 8 emits.
const DEPTH: u64 = 24;

fn campaign<'a>(validator: &'a NativeValidator, tests: &'a [TestCase], depth: u64) -> Campaign<'a> {
    Campaign {
        validator,
        module: "CONSOLE",
        observation: &[],
        classify: &normal,
        tests,
        budget: ExecutionBudget {
            time: NO_CLOCK,
            max_simplification_iterations: 10_000,
            max_depth: Some(depth),
            max_breadth: None,
        },
    }
}

const TICK: &str = "CONSOLE.tick";
const EMIT: &str = "CONSOLE.emit";
const HALT: &str = "CONSOLE.halt";
const STALL: &str = "CONSOLE.stall";
const IDLE: &str = "CONSOLE.idle";

/// An end at `done` is a crash; every other end is normal.
fn done_crashes(end: &Pattern) -> ExecutionTerminalKind {
    if k_rust::kore::printer::Printer::compact()
        .print_pattern(end)
        .contains("Lbldone")
    {
        ExecutionTerminalKind::SemanticCrash
    } else {
        ExecutionTerminalKind::Normal
    }
}

/// The point class `clock`: `<n>` before each tick.
fn clock(stutter: Stutter) -> PointClass {
    PointClass {
        name: "clock".into(),
        before: BTreeSet::from([TICK.to_owned()]),
        after: BTreeSet::new(),
        cells: vec!["n".into()],
        stutter,
    }
}

/// The point class `emitted`: after each emit, with no content.
fn emitted() -> PointClass {
    PointClass {
        name: "emitted".into(),
        before: BTreeSet::new(),
        after: BTreeSet::from([EMIT.to_owned()]),
        cells: Vec::new(),
        stutter: Stutter::Collapse,
    }
}

/// The point class `stalled`: `<phase>` before each stall, counted.
fn stalled() -> PointClass {
    PointClass {
        name: "stalled".into(),
        before: BTreeSet::from([STALL.to_owned()]),
        after: BTreeSet::new(),
        cells: vec!["phase".into()],
        stutter: Stutter::Count,
    }
}

/// The point class `control`: `<k>` before each tick.
fn control() -> PointClass {
    PointClass {
        name: "control".into(),
        before: BTreeSet::from([TICK.to_owned()]),
        after: BTreeSet::new(),
        cells: vec!["k".into()],
        stutter: Stutter::Collapse,
    }
}

/// The log `out`, read at the events of `at`.
fn out(at: &str) -> Log {
    out_at(&[at])
}

/// The log `out`, read at the events of each class of `at` and where the path ends.
fn out_at(at: &[&str]) -> Log {
    Log {
        name: "out".into(),
        cell: "out".into(),
        at: at.iter().map(|class| (*class).into()).collect(),
    }
}

fn observe(points: Vec<PointClass>, logs: Vec<Log>) -> RunOptions {
    RunOptions {
        observe: Observe::new(points, logs).unwrap(),
        ..RunOptions::default()
    }
}

/// The reference to the only Int token `token` of rule `rule` whose operation also reads the
/// variable `beside` (`N +Int 1` beside `N`, not `P +Int 1`), or of the rule anywhere without it.
fn token(baseline: &Baseline, rule: &str, token: &str, beside: Option<&str>) -> TermRef {
    fn walk(b: &Baseline, at: &TermRef, token: &str, out: &mut Vec<TermRef>) {
        let Some(term) = b.term(at) else {
            return;
        };
        if matches!(term.unannotated(), Term::Token { token: t, .. } if t == token) {
            out.push(at.clone());
        }
        for index in 0.. {
            let mut path = at.path.0.clone();
            path.push(index);
            let child = TermRef::new(at.sentence.clone(), path);
            if b.term(&child).is_none() {
                break;
            }
            walk(b, &child, token, out);
        }
    }
    let sentence = support::rule(baseline, rule);
    let mut found = Vec::new();
    for part in 0..3 {
        walk(
            baseline,
            &TermRef::new(sentence.clone(), [part]),
            token,
            &mut found,
        );
    }
    // A variable operand is read through its sort cast (`#SemanticCastToInt(N)`).
    fn reads(term: &Term, variable: &str) -> bool {
        match term.unannotated() {
            Term::Variable { name, .. } => name == variable,
            Term::Apply { arguments, .. } => arguments.iter().any(|a| reads(a, variable)),
            _ => false,
        }
    }
    found.retain(|at| {
        beside.is_none_or(|beside| {
            let parent = TermRef::new(at.sentence.clone(), &at.path.0[..at.path.0.len() - 1]);
            baseline
                .term(&parent)
                .is_some_and(|operation| reads(operation, beside))
        })
    });
    let [at] = found
        .try_into()
        .unwrap_or_else(|found: Vec<_>| panic!("{rule}: {} tokens {token}", found.len()));
    at
}

/// The one-candidate generation of `patch` at the site `site` of the rule labelled `label`.
fn generation<'b>(
    baseline: &'b Baseline,
    label: &str,
    (site, patch): (TermRef, Patch),
) -> CandidateGeneration<'b> {
    let discovery = derive_sites(
        baseline,
        "site",
        &[
            SiteSelector::RuleLabel(label.into()),
            SiteSelector::Path(site.path.0.clone()),
        ],
    )
    .unwrap();
    let generation = select(&discovery, SelectionPolicy::Each, 1)
        .unwrap()
        .fold("observe", |_| patch.clone())
        .unwrap();
    assert_eq!(
        generation.candidates().len(),
        1,
        "{:?}",
        generation.dispositions()
    );
    generation
}

/// The Int token `from` of rule `rule` becomes `to` (the one beside `N` in `tick`).
fn replaced<'b>(
    baseline: &'b Baseline,
    rule: &str,
    from: &str,
    to: &str,
) -> CandidateGeneration<'b> {
    let at = token(baseline, rule, from, (rule == TICK).then_some("N"));
    let patch = Patch::new(vec![Edit::ReplaceTerm {
        expected: baseline.term(&at).unwrap().clone(),
        at: at.clone(),
        replacement: Term::Token {
            token: to.into(),
            sort: Sort::new("Int"),
        },
    }])
    .unwrap();
    generation(baseline, rule, (at, patch))
}

/// `done` is no constructor: a rule `done => run [anywhere]` is inserted at the module's end, so
/// the compiled mutant declares `Lbldone` without `constructor` where the baseline declares a
/// constructor. No run of `run` reaches `done`. The site is halt's, whose right-hand side is it.
fn done_anywhere(baseline: &Baseline) -> CandidateGeneration<'_> {
    fn find<'t>(term: &'t Term, label: &str) -> Option<&'t Term> {
        match term.unannotated() {
            Term::Apply {
                label: head,
                arguments,
            } => (head.name == label)
                .then_some(term)
                .or_else(|| arguments.iter().find_map(|argument| find(argument, label))),
            Term::Rewrite { left, right } => find(left, label).or_else(|| find(right, label)),
            _ => None,
        }
    }
    let halt = support::rule(baseline, HALT);
    let Some(Sentence::Rule { body, .. }) = baseline.sentence(&halt) else {
        panic!("halt is a rule");
    };
    let done = find(body, "done").expect("halt rewrites to done").clone();
    let run = find(body, "run").expect("halt rewrites run").clone();
    let truth = || Term::Token {
        token: "true".into(),
        sort: Sort::new("Bool"),
    };
    // `anywhere` takes no value, as `function` does: the value `show`'s production gives it.
    let (_, show) = baseline
        .authored_sentences()
        .find(|(_, sentence)| sentence.attributes().has(AttributeKey::Function))
        .expect("show's production");
    let mut attributes = Attributes::default();
    attributes.set(
        AttributeKey::Anywhere,
        show.attributes()
            .value(AttributeKey::Function)
            .unwrap()
            .clone(),
    );
    let patch = Patch::new(vec![Edit::InsertSentence {
        position: InsertPosition::ModuleEnd("CONSOLE".into()),
        ordinal: 0,
        sentence: Sentence::Rule {
            body: Term::Rewrite {
                left: Box::new(done),
                right: Box::new(run),
            },
            requires: truth(),
            ensures: truth(),
            attributes,
        },
    }])
    .unwrap();
    generation(baseline, HALT, (TermRef::new(halt, [0]), patch))
}

/// tick is deleted.
fn tick_deleted(baseline: &Baseline) -> CandidateGeneration<'_> {
    let tick = support::rule(baseline, TICK);
    let patch = Patch::new(vec![Edit::DeleteSentence { at: tick.clone() }]).unwrap();
    generation(baseline, TICK, (TermRef::new(tick, [0]), patch))
}

fn run(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    run: RunOptions,
) -> CampaignRun {
    run_campaign_with(
        campaign,
        generation,
        &CampaignOptions {
            schedule: ScheduleMode::Full,
            selection: Sel::None,
            share_evidence: true,
            run,
            compile_workers: 1,
        },
    )
    .unwrap()
}

fn on_a_big_stack(work: impl FnOnce() + Send + 'static) {
    std::thread::Builder::new()
        .stack_size(256 << 20)
        .spawn(work)
        .unwrap()
        .join()
        .unwrap();
}

/// The one mutant's verdict on the one test's observation slot.
fn verdict(run: &CampaignRun) -> ObservationVerdict {
    match &run.mutants[0].evidence[0].notes.observation {
        Some(Observation::Compared(comparison)) => comparison
            .verdict
            .clone()
            .expect("the pair judged the slot"),
        other => panic!("no comparison: {other:?}"),
    }
}

fn position(channel: &str, index: usize, at_end: bool) -> Option<Position> {
    Some(Position {
        channel: channel.into(),
        index,
        at_end,
        outside: None,
    })
}

/// tick's count step 1 becomes 2: before each tick the count is 0, 2, 4, ... where the
/// baseline's is 0, 1, 2, ..., so the mutant is killed at the clock's element 1, within the
/// baseline's prefix (16 ticks before its depth bound); the prefix program's end slot compares
/// nothing. The baseline's record is the prefix it explored.
#[test]
fn a_faster_tick_is_killed_at_element_one_of_a_prefix_program() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), TICK, "1", "2");
        let run = run(
            &campaign,
            &generation,
            observe(vec![clock(Stutter::Collapse)], Vec::new()),
        );
        let Some(Observation::Recorded(record)) = &run.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert!(record.prefix);
        assert_eq!(record.channels[0].elements.len(), 16);
        assert!(matches!(record.channels[0].end, ChannelEnd::Open(_)));
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(
            run.mutants[0].plan.tests[0].run,
            TestRun::Compared(vec![OracleOutcome::Agree, OracleOutcome::Distinguish])
        );
        assert_eq!(verdict(&run).position, position("clock", 1, false));
    });
}

/// tick's count step 1 becomes 0: the count never moves, while the phase still runs and the
/// mutant emits a 0 where the baseline emits 2.
/// - Under `collapse` the clock channel goes silent after its first element (every later
///   content equals it), so nothing distinguishes it within the bound: `unknown`.
/// - Under `count` each tick is an element, and element 1 is 0 against 1: killed.
/// - With the out log, the mutant's first item 0 differs from the baseline's 2: killed by the
///   log, but only where the baseline emits within its prefix; under a depth bound of 2 the
///   baseline emits nothing, the log agrees up to its horizon 0, and the silent clock leaves the
///   mutant `unknown`.
#[test]
fn an_idle_mutant_is_unknown_under_collapse_and_killed_under_count_or_by_the_log() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let generation = replaced(validator.baseline(), TICK, "1", "0");
        let long = campaign(&validator, &tests, DEPTH);
        let collapsed = run(
            &long,
            &generation,
            observe(vec![clock(Stutter::Collapse)], Vec::new()),
        );
        assert_eq!(collapsed.mutants[0].report.status, MutantStatus::Unknown);
        assert_eq!(verdict(&collapsed).outcome, OracleOutcome::Unknown);
        let counted = run(
            &long,
            &generation,
            observe(vec![clock(Stutter::Count)], Vec::new()),
        );
        assert_eq!(counted.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&counted).position, position("clock", 1, false));
        let logged = observe(vec![clock(Stutter::Collapse)], vec![out("clock")]);
        let by_log = run(&long, &generation, logged);
        assert_eq!(by_log.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&by_log).position, position("out", 0, false));
        let short = campaign(&validator, &tests, 2);
        let unseen = run(&short, &generation, logged);
        assert_eq!(unseen.mutants[0].report.status, MutantStatus::Unknown);
        let unseen = verdict(&unseen);
        assert_eq!(unseen.outcome, OracleOutcome::Unknown);
        assert!(unseen.cause.unwrap().contains("clock"));
    });
}

/// halt's bound becomes 2: the mutant ends (`done`, a clean ground stuck end) where the
/// baseline's clock has its element 3, so END distinguishes against that content element.
#[test]
fn a_mutant_that_ends_early_is_killed_by_its_end() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), "CONSOLE.halt", "1000000", "2");
        let run = run(
            &campaign,
            &generation,
            observe(vec![clock(Stutter::Collapse)], Vec::new()),
        );
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&run).position, position("clock", 3, true));
    });
}

/// stall's bound becomes 2: after the clock's elements 0, 1 and 2, which agree, the mutant
/// runs on without another tick and never ends. No finite prefix of its observation differs
/// from the baseline's, so it is `unknown` under either stuttering mode: a bound never kills.
#[test]
fn silent_divergence_after_agreement_is_unknown() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), "CONSOLE.stall", "1000000", "2");
        for stutter in [Stutter::Collapse, Stutter::Count] {
            let run = run(
                &campaign,
                &generation,
                observe(vec![clock(stutter)], Vec::new()),
            );
            assert_eq!(
                run.mutants[0].report.status,
                MutantStatus::Unknown,
                "{stutter:?}"
            );
            assert_eq!(verdict(&run).outcome, OracleOutcome::Unknown, "{stutter:?}");
        }
    });
}

/// idle's -1000 becomes 3: after its third tick the mutant's count is 3, where `idle` sets the
/// phase to 7 and then rewrites 7 to 7. Its path returns at depth 6 to its state at depth 5 with
/// nothing new observed, so it runs forever and its clock never has another element; a run to the
/// bound alone could only say `unknown`, as for a silent divergence. The baseline's clock has its
/// element 3 within its prefix, a decided difference: killed at clock 3 under either stuttering
/// mode. A declaration of the out log alone, read where the path ends, is decided alike: the
/// return reads the log once more, its one item 2 agrees, and the baseline's item 1 is a decided
/// difference. With room for one state only the state at depth 4 is kept, the return to depth 5
/// is past the room, no cycle is claimed, and the mutant is `unknown`.
#[test]
fn an_idle_forever_mutant_is_killed_by_its_return_where_the_baseline_still_emits() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), IDLE, "-1000", "3");
        for stutter in [Stutter::Collapse, Stutter::Count] {
            let run = run(
                &campaign,
                &generation,
                observe(vec![clock(stutter)], Vec::new()),
            );
            assert_eq!(
                run.mutants[0].report.status,
                MutantStatus::Killed,
                "{stutter:?}"
            );
            let verdict = verdict(&run);
            assert_eq!(verdict.position, position("clock", 3, false), "{stutter:?}");
            assert_eq!(verdict.cycle, Some((5, 6)), "{stutter:?}");
        }
        let logged = run(
            &campaign,
            &generation,
            observe(Vec::new(), vec![out_at(&[])]),
        );
        assert_eq!(logged.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&logged).position, position("out", 1, false));
        let roomless = RunOptions {
            observe: Observe::new(vec![clock(Stutter::Collapse)], Vec::new())
                .unwrap()
                .with_cycle_states(1),
            ..RunOptions::default()
        };
        let run = run(&campaign, &generation, roomless);
        assert_eq!(run.mutants[0].report.status, MutantStatus::Unknown);
        let verdict = verdict(&run);
        assert_eq!(verdict.outcome, OracleOutcome::Unknown);
        assert_eq!(verdict.cycle, None);
    });
}

/// From -1003 the baseline's count reaches -1000 after three ticks and idles there: its path
/// returns at depth 6 to its state at depth 5 with nothing new observed, so its clock is complete
/// and silent after -1003, -1002 and -1001, though its run goes on to its depth bound as without
/// the probe, a prefix program.
/// - emit's phase reset 0 becomes 1: the mutant ticks at the same counts, idles alike and returns
///   too, so it agrees on everything and survives with no horizon.
/// - idle's -1000 becomes 3: the mutant ticks on, and its clock's element 3 against the
///   baseline's silence is a decided difference.
#[test]
fn a_baseline_that_returns_closes_its_channels_complete_and_silent() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test_from("idle", -1003, CrashPolicy::Reject)];
        let campaign = campaign(&validator, &tests, DEPTH);
        let options = observe(vec![clock(Stutter::Collapse)], Vec::new());
        let alike = run(
            &campaign,
            &replaced(validator.baseline(), EMIT, "0", "1"),
            options,
        );
        let Some(Observation::Recorded(record)) = &alike.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert!(record.prefix);
        assert_eq!(record.channels[0].elements.len(), 3);
        assert_eq!(
            record.channels[0].end,
            ChannelEnd::Closed(kink_campaign::Closure::Cycle)
        );
        assert_eq!(alike.mutants[0].report.status, MutantStatus::Survived);
        let agreed = verdict(&alike);
        assert_eq!(agreed.outcome, OracleOutcome::Agree);
        assert!(agreed.horizon.is_empty());
        assert_eq!(agreed.cycle, Some((5, 6)));
        let onwards = run(
            &campaign,
            &replaced(validator.baseline(), IDLE, "-1000", "3"),
            options,
        );
        assert_eq!(onwards.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&onwards).position, position("clock", 3, false));
    });
}

/// tick is deleted: the point class names no rewrite rule of the mutant, so the mutant is not
/// admitted (`point-unresolved`) before any test runs; no kill rests on an edit of a label.
#[test]
fn a_mutant_without_a_point_rule_is_not_admitted() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = tick_deleted(validator.baseline());
        let run = run(
            &campaign,
            &generation,
            observe(vec![clock(Stutter::Collapse)], Vec::new()),
        );
        let mutant = &run.mutants[0];
        assert_eq!(
            mutant.plan.mutant_failure,
            Some(MutantScopeFailure::PointUnresolved)
        );
        assert_eq!(mutant.report.status, MutantStatus::NotAdmitted);
        assert!(mutant.plan.tests.is_empty());
    });
}

/// The baseline's third item `show(6)` is no value (`show` has a value only below 5), so its
/// log opens there, at horizon 2. tick's count step 2 makes the mutant's first item 4 against
/// the baseline's 2: a decided difference before the undecided element still kills. tick's count
/// step 3 makes the mutant's own first item `show(6)`, no value: its log opens at 0, before any
/// difference, and the mutant is `unknown`.
#[test]
fn an_undecided_element_opens_the_channel_while_an_earlier_difference_still_kills() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let options = observe(vec![emitted()], vec![out("emitted")]);
        let faster = replaced(validator.baseline(), TICK, "1", "2");
        let killed = run(&campaign, &faster, options);
        let Some(Observation::Recorded(record)) = &killed.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert_eq!(record.channels[1].horizon(), Some(2));
        assert_eq!(killed.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&killed).position, position("out", 0, false));
        let residue = replaced(validator.baseline(), TICK, "1", "3");
        let unknown = run(&campaign, &residue, options);
        assert_eq!(unknown.mutants[0].report.status, MutantStatus::Unknown);
        let cause = verdict(&unknown).cause.unwrap();
        assert!(cause.contains("out"), "{cause}");
    });
}

/// jump's -1 becomes 1: at the second tick both tick and jump apply, so the mutant's run splits
/// there (kink-campaign `observation`, "Several paths"). Its tick path agrees with the baseline's
/// one path, and its jump path's clock prefix [0, 101] is no prefix of the baseline, which is
/// explored to its horizon of 16 on its one path: the mutant's prefix is outside the baseline's
/// set at clock index 1, and the mutant is killed there. A branch where the baseline is not
/// explored to the index stays unknown (`several_paths::incomplete_exploration_stays_unknown`).
#[test]
fn a_branching_mutants_path_outside_the_baseline_set_kills() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), "CONSOLE.jump", "-1", "1");
        let run = run(
            &campaign,
            &generation,
            observe(vec![clock(Stutter::Count)], Vec::new()),
        );
        assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
        let verdict = verdict(&run);
        assert_eq!(verdict.outcome, OracleOutcome::Distinguish);
        assert_eq!(
            verdict.position,
            Some(Position {
                channel: "clock".into(),
                index: 1,
                at_end: false,
                outside: Some(kink_campaign::Outside::Mutant),
            })
        );
    });
}

/// tick's count step 2 under a mutant work budget: with room for two states the mutant's
/// first difference (element 1, its second tick) is within its explored prefix, and it is
/// killed there; with room for one the budget ends the run first, and a bound never kills.
#[test]
fn a_work_bound_mutant_is_killed_on_its_explored_prefix() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), TICK, "1", "2");
        let budget = |floor| RunOptions {
            work: WorkBudget::Calibrated { factor: 0, floor },
            ..observe(vec![clock(Stutter::Collapse)], Vec::new())
        };
        let killed = run(&campaign, &generation, budget(8));
        assert_eq!(killed.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&killed).position, position("clock", 1, false));
        let bounded = run(&campaign, &generation, budget(1));
        assert_eq!(bounded.mutants[0].report.status, MutantStatus::Unknown);
    });
}

/// Without a declaration nothing moves: the console never ends, so its baseline has no end to
/// compare and the campaign is refused as it was before observations existed; the run options'
/// record names no `observe`.
#[test]
fn without_a_declaration_the_console_is_refused_as_before() {
    on_a_big_stack(|| {
        assert!(RunOptions::default().value().get("observe").is_none());
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), TICK, "1", "2");
        let refused = run_campaign_with(
            &campaign,
            &generation,
            &CampaignOptions {
                schedule: ScheduleMode::Full,
                selection: Sel::None,
                share_evidence: true,
                run: RunOptions::default(),
                compile_workers: 1,
            },
        )
        .unwrap_err();
        assert_eq!(refused.kind(), CampaignFailureKind::BaselineOracleFailed);
        let observed = observe(vec![clock(Stutter::Collapse)], Vec::new());
        assert!(observed.value().get("observe").is_some());
    });
}

/// The campaign's refusal of its baseline.
fn refusal(
    campaign: &Campaign<'_>,
    generation: &CandidateGeneration<'_>,
    run: RunOptions,
) -> kink_campaign::CampaignFailure {
    run_campaign_with(
        campaign,
        generation,
        &CampaignOptions {
            schedule: ScheduleMode::Full,
            selection: Sel::None,
            share_evidence: true,
            run,
            compile_workers: 1,
        },
    )
    .map(|_| ())
    .unwrap_err()
}

/// Eight steps are four ticks and two emits: the out log, read only where the path ends, holds
/// 2 and 4 at the baseline's depth bound, its horizon. A log item the last step appended, read
/// where the mutant's path ended (its own depth bound, so its end is not determined), that differs
/// from the baseline's at the index is a decided difference on a settled leaf, never an
/// agreement up to the horizon:
/// - emit's phase reset 0 becomes 1: the mutant's items are 2, 3, 4, so its item 1, the
///   baseline's last recorded one, is 3 against 4;
/// - tick's count step 1 becomes 2: its first item is 4 against 2.
#[test]
fn a_log_item_read_where_a_bounded_path_ended_is_killed() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, 8);
        let logged = observe(Vec::new(), vec![out_at(&[])]);
        let late = replaced(validator.baseline(), EMIT, "0", "1");
        let killed = run(&campaign, &late, logged);
        let Some(Observation::Recorded(record)) = &killed.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert!(record.prefix);
        assert_eq!(record.channels[0].horizon(), Some(2));
        assert_eq!(killed.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&killed).position, position("out", 1, true));
        let faster = replaced(validator.baseline(), TICK, "1", "2");
        let killed = run(&campaign, &faster, logged);
        assert_eq!(killed.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&killed).position, position("out", 0, true));
    });
}

/// Two steps are two ticks: the out log, read where the path ends, is empty at the baseline's
/// depth bound, so its only channel's horizon is 0. A mutant that agrees with it agrees on
/// nothing: `unknown`, naming the empty horizon, never `survived`.
#[test]
fn a_prefix_that_observed_nothing_leaves_its_mutant_unknown() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, 2);
        let generation = replaced(validator.baseline(), TICK, "1", "2");
        let run = run(
            &campaign,
            &generation,
            observe(Vec::new(), vec![out_at(&[])]),
        );
        assert_eq!(run.mutants[0].report.status, MutantStatus::Unknown);
        let verdict = verdict(&run);
        assert_eq!(verdict.outcome, OracleOutcome::Unknown);
        assert!(verdict.cause.unwrap().contains("horizon is 0"));
    });
}

/// emit's phase reset 0 becomes 1: the mutant emits every second step where the baseline emits
/// every third. Counting emits with no content, the baseline's prefix has 8; the mutant's ninth
/// emit reaches that horizon, its probe ends the request (`Done`), and it survives with the
/// horizon 8: no difference within what the baseline observed.
#[test]
fn a_mutant_that_agrees_up_to_the_horizon_survives_with_it() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), EMIT, "0", "1");
        let counted = PointClass {
            stutter: Stutter::Count,
            ..emitted()
        };
        let run = run(&campaign, &generation, observe(vec![counted], Vec::new()));
        assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        assert_eq!(
            run.mutants[0].plan.tests[0].run,
            TestRun::Compared(vec![OracleOutcome::Agree, OracleOutcome::Agree])
        );
        let verdict = verdict(&run);
        assert_eq!(verdict.outcome, OracleOutcome::Agree);
        assert_eq!(
            verdict.horizon,
            std::collections::BTreeMap::from([(
                "emitted".to_owned(),
                kink_campaign::Horizon {
                    elements: 8,
                    opening: kink_campaign::Opening::Bound,
                }
            )])
        );
    });
}

/// From a count of 1000001 the baseline halts at once (`done`, a clean ground end), closing
/// every channel with END before any element. halt's bound 1000000 becomes 999999: the mutant
/// halts alike, every channel agrees to its end, and it survives with no horizon. It becomes
/// 1000001: the mutant stalls instead, and its first stall's content is distinguished from the
/// baseline's END.
#[test]
fn a_baseline_that_ends_closes_its_channels_with_end() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test_from("halted", 1_000_001, CrashPolicy::Reject)];
        let campaign = campaign(&validator, &tests, DEPTH);
        let options = observe(vec![clock(Stutter::Collapse), stalled()], Vec::new());
        let alike = replaced(validator.baseline(), HALT, "1000000", "999999");
        let survived = run(&campaign, &alike, options);
        let Some(Observation::Recorded(record)) = &survived.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert!(!record.prefix);
        for channel in &record.channels {
            assert!(channel.elements.is_empty());
            assert_eq!(channel.end, ChannelEnd::Closed(kink_campaign::Closure::End));
        }
        assert_eq!(survived.mutants[0].report.status, MutantStatus::Survived);
        let agreed = verdict(&survived);
        assert_eq!(agreed.outcome, OracleOutcome::Agree);
        assert!(agreed.horizon.is_empty());
        let stalling = replaced(validator.baseline(), HALT, "1000000", "1000001");
        let killed = run(&campaign, &stalling, options);
        assert_eq!(killed.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&killed).position, position("stalled", 0, false));
    });
}

/// `done` is no constructor on the mutant: an inserted `anywhere` rule heads it, so the mutant
/// declares the symbol `Lbldone`, which the `<k>` cell reaches through `KItem`, otherwise than
/// the baseline. A content that reads `<k>` would be read with the baseline's declarations, so
/// the mutant is not admitted (`observation-incompatible`) before any test runs.
#[test]
fn a_mutant_declaring_a_read_constructor_otherwise_is_not_admitted() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = done_anywhere(validator.baseline());
        let refused = run(&campaign, &generation, observe(vec![control()], Vec::new()));
        let mutant = &refused.mutants[0];
        assert_eq!(
            mutant.plan.mutant_failure,
            Some(MutantScopeFailure::ObservationIncompatible)
        );
        assert_eq!(mutant.report.status, MutantStatus::NotAdmitted);
        assert!(mutant.plan.tests.is_empty());
    });
}

/// From a count of -50 the run has two paths at once: `fall` ends at `done`, which this
/// campaign classifies as a crash, and `tick` runs on to the depth bound. The baseline is a
/// prefix program, whose end sides admission does not read, but its crashing path still meets
/// the slot's crash policy: a slot that rejects a crash refuses the baseline, and one that
/// compares crashes admits it.
#[test]
fn a_prefix_program_with_a_crashing_path_meets_the_crash_policy() {
    on_a_big_stack(|| {
        let validator = validator();
        let generation = replaced(validator.baseline(), TICK, "1", "2");
        let options = observe(vec![clock(Stutter::Collapse)], Vec::new());
        let rejecting = [test_from("fall", -50, CrashPolicy::Reject)];
        let rejected = Campaign {
            classify: &done_crashes,
            ..campaign(&validator, &rejecting, DEPTH)
        };
        let refused = refusal(&rejected, &generation, options);
        assert_eq!(refused.kind(), CampaignFailureKind::BaselineOracleFailed);
        let comparing = [test_from("fall", -50, CrashPolicy::CompareIdentity)];
        let compared = Campaign {
            classify: &done_crashes,
            ..campaign(&validator, &comparing, DEPTH)
        };
        let admitted = run(&compared, &generation, options);
        let Some(Observation::Recorded(record)) = &admitted.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert!(record.prefix && record.crashed);
    });
}

/// From a count of -22 the first emit appends -20, which `rewrite` then replaces by 0: the
/// out log, read after each emit, holds 0 where it held -20, so its cell did not only grow by
/// appending. Its channel is no concatenation of appended items, and the baseline's campaign
/// is refused (`log-not-appended`).
#[test]
fn a_baseline_log_that_is_rewritten_refuses_the_campaign() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test_from("rewritten", -22, CrashPolicy::Reject)];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), TICK, "1", "2");
        let refused = refusal(
            &campaign,
            &generation,
            observe(vec![emitted()], vec![out("emitted")]),
        );
        assert_eq!(refused.kind(), CampaignFailureKind::BaselineOracleFailed);
        let message = refused.to_string();
        assert!(message.contains("log-not-appended"), "{message}");
    });
}

/// From `<phase> f(h(0)) </phase>` and `<out> ListItem(h(0)) </out>` the baseline runs as from a
/// count of 0 with the log's first item 1: eight steps hold 1, 2 and 4, read where the path ends.
/// h's step 1 becomes 20: the mutant's initial configuration holds `f(20)`, which `f`'s `#Ceil`
/// lemma shows to have no instance, so k-rust refutes the configuration's own definedness facts
/// and gives one `Vacuous` leaf, whose state is the configuration with no `\bottom` added and its
/// log's item 20. The probe is told that the path ended there and reads 20 against the baseline's
/// 1, but no model of the mutant has an instance of that state, so no path of it reads that log:
/// the difference is not decided, and the mutant is `unknown`, never killed.
#[test]
fn a_vacuous_leaf_kills_nothing_by_what_it_holds() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [TestCase {
            id: "vacuous".into(),
            initial_state: console_holding(
                r#"Lblf{}(Lblh{}(\dv{SortInt{}}("0")))"#,
                r#"LblListItem{}(inj{SortInt{}, SortKItem{}}(Lblh{}(\dv{SortInt{}}("0"))))"#,
            ),
            oracles: vec![
                OracleDeclaration::new(
                    CrashPolicy::Reject,
                    Projection::State(StateProjection::WholeTerm),
                )
                .unwrap(),
            ],
        }];
        let campaign = campaign(&validator, &tests, 8);
        let generation = replaced(validator.baseline(), "CONSOLE.h", "1", "20");
        let run = run(
            &campaign,
            &generation,
            observe(Vec::new(), vec![out_at(&[])]),
        );
        let Some(Observation::Recorded(record)) = &run.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert!(record.prefix);
        assert_eq!(record.channels[0].horizon(), Some(3));
        let verdict = verdict(&run);
        assert_eq!(verdict.outcome, OracleOutcome::Unknown, "{verdict:?}");
        let cause = verdict.cause.unwrap();
        assert!(
            cause.contains("differs at 0 where the path ended"),
            "{cause}"
        );
        assert_eq!(run.mutants[0].report.status, MutantStatus::Unknown);
    });
}

/// Twenty-four steps from a count of 0 append 2, 4 and `show(6)`, ...: `show` is total, so its
/// irreducible application owes no definedness, and the baseline's leaf state, though it holds
/// it, is shown to exist and is real. The out log, read where the path ends, keeps 2 and 4 and
/// opens at `show(6)`, which is no value: its element is undecided, not its state.
#[test]
fn a_total_residue_leaves_its_state_real_and_its_element_undecided() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), TICK, "1", "2");
        let run = run(
            &campaign,
            &generation,
            observe(Vec::new(), vec![out_at(&[])]),
        );
        let Some(Observation::Recorded(record)) = &run.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert_eq!(record.channels[0].horizon(), Some(2));
        let ChannelEnd::Open(opened) = &record.channels[0].end else {
            panic!("the log opens at the residue");
        };
        assert_eq!(
            opened.opening,
            kink_campaign::Opening::UndecidedElement,
            "{opened:?}"
        );
        assert!(!opened.reason.contains("not settled"), "{opened:?}");
    });
}

/// A front end's functions of an observer for the `clock` class: an event only where the count
/// is even (the filter), whose content is the count halved, as the function gives it, with its
/// value. Its identity names them.
struct Halved;

impl ObservationFunctions for Halved {
    fn cells(&self) -> &[Vec<String>] {
        &[]
    }

    fn filtered(&self, _: usize) -> bool {
        true
    }

    fn with_evaluator(
        &self,
        body: &mut dyn FnMut(&mut dyn ObservationEvaluator),
    ) -> Result<(), String> {
        body(&mut Halved);
        Ok(())
    }
}

/// The count `<n>` of `state`, where it is a literal.
fn count_of(state: &ProbeState<'_>) -> Result<i64, String> {
    fn find(pattern: &Pattern) -> Option<i64> {
        match pattern {
            Pattern::Application { symbol, arguments } if symbol.name == "Lbl'-LT-'n'-GT-'" => {
                match arguments.as_slice() {
                    [Pattern::DomainValue { value, .. }] => value.as_utf8().ok()?.parse().ok(),
                    _ => None,
                }
            }
            Pattern::Application { arguments, .. } => arguments.iter().find_map(find),
            _ => None,
        }
    }
    find(&state.configuration()).ok_or_else(|| "the count is no literal".to_owned())
}

impl ObservationEvaluator for Halved {
    fn holds(&mut self, _: usize, state: &ProbeState<'_>) -> Option<Result<bool, String>> {
        Some(count_of(state).map(|n| n % 2 == 0))
    }

    fn content(
        &mut self,
        _: usize,
        state: &ProbeState<'_>,
        value: bool,
    ) -> Result<Evaluated, String> {
        let half = count_of(state)? / 2;
        let mut digest = [0; 32];
        digest[..8].copy_from_slice(&half.to_le_bytes());
        Ok(Evaluated {
            digest,
            value: value.then(|| serde_json::json!(half)),
        })
    }

    fn elements(&mut self, _: usize, _: &Pattern, _: bool) -> Result<Vec<Evaluated>, String> {
        Err("no log".to_owned())
    }

    fn item_digest(&mut self, _: &Pattern) -> [u8; 32] {
        [0; 32]
    }
}

/// The clock observed through a front end's functions ([`Halved`]): the baseline's events are
/// the even counts 0, 2, ..., 14 of its sixteen ticks, its elements 0 to 7. tick's count step 1
/// becomes 3: the mutant's even counts are 0, 6, 12, ..., its element 1 is 3 against the
/// baseline's 1, so it is killed there, with the function's value as its element. It becomes 2:
/// every count is even and its halves are the baseline's, so the mutant agrees up to the
/// baseline's horizon of 8 elements and survives with it, though its counts differ: the
/// functions observe what they compute, never more. The declaration's value names the functions'
/// identity, and the declaration without them keeps its value.
#[test]
fn a_front_ends_functions_give_the_contents_and_filter_the_events() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let plain = Observe::new(vec![clock(Stutter::Collapse)], Vec::new()).unwrap();
        let identity = serde_json::json!({"halved": 1});
        let declared = plain.with_functions(ObserveFunctions::new(
            identity.clone(),
            std::sync::Arc::new(Halved),
        ));
        assert_eq!(declared.value().unwrap()["functions"], identity);
        assert!(plain.value().unwrap().get("functions").is_none());
        let options = RunOptions {
            observe: declared,
            ..RunOptions::default()
        };
        let faster = replaced(validator.baseline(), TICK, "1", "3");
        let killed = run(&campaign, &faster, options);
        let Some(Observation::Recorded(record)) = &killed.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert_eq!(record.channels[0].elements.len(), 8);
        assert_eq!(killed.mutants[0].report.status, MutantStatus::Killed);
        let distinguished = verdict(&killed);
        assert_eq!(distinguished.position, position("clock", 1, false));
        assert_eq!(
            distinguished.element,
            Some(Element::Evaluated(serde_json::json!(3)))
        );
        let even = replaced(validator.baseline(), TICK, "1", "2");
        let survived = run(&campaign, &even, options);
        assert_eq!(survived.mutants[0].report.status, MutantStatus::Survived);
        assert_eq!(
            verdict(&survived).horizon,
            std::collections::BTreeMap::from([(
                "clock".to_owned(),
                kink_campaign::Horizon {
                    elements: 8,
                    opening: kink_campaign::Opening::Bound,
                }
            )])
        );
    });
}

/// A front end whose observer gave no request an evaluator: it reads `cells` besides the
/// declaration's, and says whether its class has a filter (`filtered`).
struct Unloaded {
    cells: Vec<Vec<String>>,
    filtered: bool,
}

impl ObservationFunctions for Unloaded {
    fn cells(&self) -> &[Vec<String>] {
        &self.cells
    }

    fn filtered(&self, _: usize) -> bool {
        self.filtered
    }

    fn with_evaluator(
        &self,
        _: &mut dyn FnMut(&mut dyn ObservationEvaluator),
    ) -> Result<(), String> {
        Err("the observer does not load".to_owned())
    }
}

/// `observe` with `functions` set on its declaration, whose identity is `identity`: equal
/// declarations are one interned value with one oracle, so each distinct oracle names its own.
fn with_functions(
    options: RunOptions,
    identity: serde_json::Value,
    functions: impl ObservationFunctions + 'static,
) -> RunOptions {
    RunOptions {
        observe: options.observe.with_functions(ObserveFunctions::new(
            identity,
            std::sync::Arc::new(functions),
        )),
        ..options
    }
}

/// An observer that gives no request an evaluator leaves every filter undecided: whether a point
/// is an event is not known, so a class with a filter opens its channel at its first point, and
/// halt's bound -1, which ends the mutant before its first tick, kills nothing there, though the
/// baseline ticks: its filter may hold at none of its ticks. A class with no filter keeps every
/// tick as an event, each an undecided element: counted, the baseline's first tick is an element
/// at 0, a fact of its path, so the mutant's END there is a decided difference.
#[test]
fn a_request_without_an_evaluator_opens_each_filtered_class_at_its_first_point() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), HALT, "1000000", "-1");
        let counted = || observe(vec![clock(Stutter::Count)], Vec::new());
        let filtered = run(
            &campaign,
            &generation,
            with_functions(
                counted(),
                serde_json::json!({"unloaded": {"filtered": true}}),
                Unloaded {
                    cells: Vec::new(),
                    filtered: true,
                },
            ),
        );
        let Some(Observation::Recorded(record)) = &filtered.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert_eq!(record.channels[0].horizon(), Some(0));
        let ChannelEnd::Open(opened) = &record.channels[0].end else {
            panic!("the filtered class opens at its first point");
        };
        assert_eq!(
            opened.opening,
            kink_campaign::Opening::UndecidedElement,
            "{opened:?}"
        );
        assert!(
            opened.reason.contains("its filter is not known here"),
            "{opened:?}"
        );
        assert_ne!(filtered.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&filtered).outcome, OracleOutcome::Unknown);

        let unfiltered = run(
            &campaign,
            &generation,
            with_functions(
                counted(),
                serde_json::json!({"unloaded": {"filtered": false}}),
                Unloaded {
                    cells: Vec::new(),
                    filtered: false,
                },
            ),
        );
        assert_eq!(unfiltered.mutants[0].report.status, MutantStatus::Killed);
        let distinguished = verdict(&unfiltered);
        assert_eq!(distinguished.position, position("clock", 0, true));
        assert_eq!(distinguished.element, Some(Element::End));
    });
}

/// [`Halved`], whose filter is not known where the count is 4: counted, the clock's events are
/// the counts 0 and 2, and its channel opens at its element 2, the point at 4, since whether that
/// point is an event is not known. tick's count step 1 becomes 3: the mutant's even counts are 0
/// and 6, its element 1 is 3 against the baseline's 1, before the open point: killed there.
struct Unsure;

impl ObservationFunctions for Unsure {
    fn cells(&self) -> &[Vec<String>] {
        &[]
    }

    fn filtered(&self, _: usize) -> bool {
        true
    }

    fn with_evaluator(
        &self,
        body: &mut dyn FnMut(&mut dyn ObservationEvaluator),
    ) -> Result<(), String> {
        body(&mut Unsure);
        Ok(())
    }
}

impl ObservationEvaluator for Unsure {
    fn holds(&mut self, class: usize, state: &ProbeState<'_>) -> Option<Result<bool, String>> {
        match count_of(state) {
            Ok(4) => Some(Err("the filter is not known at 4".to_owned())),
            _ => Halved.holds(class, state),
        }
    }

    fn content(
        &mut self,
        class: usize,
        state: &ProbeState<'_>,
        value: bool,
    ) -> Result<Evaluated, String> {
        Halved.content(class, state, value)
    }

    fn elements(
        &mut self,
        log: usize,
        item: &Pattern,
        value: bool,
    ) -> Result<Vec<Evaluated>, String> {
        Halved.elements(log, item, value)
    }

    fn item_digest(&mut self, item: &Pattern) -> [u8; 32] {
        Halved.item_digest(item)
    }
}

/// [`Unsure`]'s filter, not known at the count 4, opens the counted clock's channel there.
#[test]
fn an_undecided_filter_opens_a_counted_class_at_its_point() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let options = with_functions(
            observe(vec![clock(Stutter::Count)], Vec::new()),
            serde_json::json!({"unsure": 4}),
            Unsure,
        );
        let faster = replaced(validator.baseline(), TICK, "1", "3");
        let killed = run(&campaign, &faster, options);
        let Some(Observation::Recorded(record)) = &killed.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        assert_eq!(record.channels[0].horizon(), Some(2));
        let ChannelEnd::Open(opened) = &record.channels[0].end else {
            panic!("the class opens at the undecided filter");
        };
        assert_eq!(
            opened.opening,
            kink_campaign::Opening::UndecidedElement,
            "{opened:?}"
        );
        assert!(
            opened.reason.contains("the filter is not known at 4"),
            "{opened:?}"
        );
        assert_eq!(killed.mutants[0].report.status, MutantStatus::Killed);
        assert_eq!(verdict(&killed).position, position("clock", 1, false));
    });
}

/// The cells a front end's functions read besides the declaration's are read cells of it, which
/// a mutant's admission reads with the declaration's: functions that read a cell no symbol of the
/// configuration heads give no read signature to compare, so the mutant whose tick steps by 3 is
/// not admitted (`observation-incompatible`), while the same functions reading `<n>`, or no other
/// cell, admit it.
#[test]
fn a_cell_a_front_ends_functions_read_is_a_read_cell_for_admission() {
    on_a_big_stack(|| {
        let validator = validator();
        let tests = [test("console")];
        let campaign = campaign(&validator, &tests, DEPTH);
        let generation = replaced(validator.baseline(), TICK, "1", "3");
        let cell = |name: &str| {
            vec![
                "Lbl'-LT-'generatedTop'-GT-'".to_owned(),
                format!("Lbl'-LT-'{name}'-GT-'"),
            ]
        };
        for (cells, refused) in [
            (Vec::new(), false),
            (vec![cell("n")], false),
            (vec![cell("nosuch")], true),
        ] {
            let options = with_functions(
                observe(vec![clock(Stutter::Count)], Vec::new()),
                serde_json::json!({"unloaded": {"cells": cells}}),
                Unloaded {
                    cells: cells.clone(),
                    filtered: false,
                },
            );
            let run = run(&campaign, &generation, options);
            let mutant = &run.mutants[0];
            assert_eq!(
                mutant.plan.mutant_failure,
                refused.then_some(MutantScopeFailure::ObservationIncompatible),
                "{cells:?}"
            );
            assert_eq!(
                mutant.report.status == MutantStatus::NotAdmitted,
                refused,
                "{cells:?}"
            );
        }
    });
}

/// Several paths (kink-campaign `observation`, "Several paths"): `testdata/k/choice.k`, a console
/// whose run from 0 takes one of three steps, so its `<out>` log's prefix set is {1, 2}, each
/// path closed by its end at `done`. The one slot reads only the end's terminal class, which
/// every end shares, so the observation slot alone decides.
mod several_paths {
    use super::*;
    use kink_campaign::Outside;

    const LEFT: &str = "CHOICE.left";
    const RIGHT: &str = "CHOICE.right";
    const EXTRA: &str = "CHOICE.extra";
    const FINISH: &str = "CHOICE.finish";

    fn choice() -> NativeValidator {
        NativeValidator::bind(
            support::load_path(&Path::new(support::DIR).join("choice.k"), "CHOICE"),
            CompileOptions::default(),
        )
    }

    /// `<k> run </k> <n> count </n> <out> .List </out>`.
    fn choice_from(count: i64) -> Pattern {
        let initial = support::initial_state(support::app("Lblrun", Vec::new()), "SortCmd");
        let Pattern::Application { symbol, arguments } = &initial else {
            unreachable!("a configuration is an application");
        };
        let cell = |name: &str, content: Pattern| {
            support::app(&format!("Lbl'-LT-'{name}'-GT-'"), vec![content])
        };
        Pattern::Application {
            symbol: symbol.clone(),
            arguments: vec![
                arguments[0].clone(),
                cell("n", support::int(count)),
                cell("out", support::app("Lbl'Stop'List", Vec::new())),
                arguments[1].clone(),
            ],
        }
    }

    fn test(count: i64) -> TestCase {
        TestCase {
            id: format!("choice-{count}"),
            initial_state: choice_from(count),
            oracles: vec![
                OracleDeclaration::new(
                    CrashPolicy::Reject,
                    Projection::State(StateProjection::ExitStop {
                        exit_code_cell: None,
                    }),
                )
                .unwrap(),
            ],
        }
    }

    fn choosing<'a>(
        validator: &'a NativeValidator,
        tests: &'a [TestCase],
        depth: u64,
    ) -> Campaign<'a> {
        Campaign {
            module: "CHOICE",
            ..campaign(validator, tests, depth)
        }
    }

    /// The class `finished`, after each finish, with no content, and the `out` log read there
    /// and where each path ends: each item is compared as the path that appended it finishes.
    fn finished() -> RunOptions {
        observe(
            vec![PointClass {
                name: "finished".into(),
                before: BTreeSet::new(),
                after: BTreeSet::from([FINISH.to_owned()]),
                cells: Vec::new(),
                stutter: Stutter::Collapse,
            }],
            vec![out("finished")],
        )
    }

    fn deleted<'b>(baseline: &'b Baseline, rule: &str) -> CandidateGeneration<'b> {
        let at = support::rule(baseline, rule);
        let patch = Patch::new(vec![Edit::DeleteSentence { at: at.clone() }]).unwrap();
        generation(baseline, rule, (TermRef::new(at, [0]), patch))
    }

    /// The baseline's record: the prefix sets of its paths.
    fn record(run: &CampaignRun) -> &kink_campaign::PathRecord {
        let Some(Observation::Recorded(record)) = &run.baseline[0].notes.observation else {
            panic!("the baseline records its channels");
        };
        record
            .paths
            .as_ref()
            .expect("the baseline's run has several paths")
    }

    fn outside(channel: &str, index: usize, side: Outside) -> Option<Position> {
        Some(Position {
            channel: channel.into(),
            index,
            at_end: false,
            outside: Some(side),
        })
    }

    /// The baseline's paths emit 1, 2 and 1 again; its record holds the log's prefixes [1] and
    /// [2] and their END, every path explored to its end, and is real. extra's -1 becomes 0: a
    /// third path appends 3, which no baseline path has at index 0, so the mutant is killed there,
    /// on the fly, at the finish of the path that appended it.
    #[test]
    fn a_mutant_with_a_third_behaviour_is_killed() {
        on_a_big_stack(|| {
            let validator = choice();
            let tests = [test(0)];
            let campaign = choosing(&validator, &tests, 8);
            let generation = replaced(validator.baseline(), EXTRA, "-1", "0");
            let run = run(&campaign, &generation, finished());
            let record = record(&run);
            assert!(record.real);
            let out = &record.channels[1];
            assert_eq!(out.complete_to, None);
            assert_eq!(out.prefixes[0].len(), 2);
            // Each path's END after its one item.
            assert_eq!(out.prefixes[1].len(), 2);
            assert_eq!(out.prefixes.len(), 2);
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
            let verdict = verdict(&run);
            assert_eq!(verdict.position, outside("out", 0, Outside::Mutant));
            assert!(matches!(verdict.element, Some(Element::Content(_))));
        });
    }

    /// right's guard 0 becomes 5: the mutant's paths emit 1 only. Every mutant path is explored to
    /// its end, so the baseline's prefix [2], which a real path of the baseline has and no path of
    /// the mutant has, kills it.
    #[test]
    fn a_mutant_that_drops_a_behaviour_is_killed() {
        on_a_big_stack(|| {
            let validator = choice();
            let tests = [test(0)];
            let generation = replaced(validator.baseline(), RIGHT, "0", "5");
            let run = run(&choosing(&validator, &tests, 8), &generation, finished());
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
            let verdict = verdict(&run);
            assert_eq!(verdict.position, outside("out", 0, Outside::Baseline));
            assert_eq!(verdict.element, None);
        });
    }

    /// left is deleted: the mutant's paths are right's, which appends 2, and again's, which
    /// appends 1, explored in another order than the baseline's. Their prefix sets are the
    /// baseline's, each explored to its end: the mutant survives with no horizon.
    #[test]
    fn a_mutant_that_reorders_the_paths_survives() {
        on_a_big_stack(|| {
            let validator = choice();
            let tests = [test(0)];
            let campaign = choosing(&validator, &tests, 8);
            let generation = deleted(validator.baseline(), LEFT);
            let run = run(&campaign, &generation, finished());
            let verdict = verdict(&run);
            assert_eq!(verdict.outcome, OracleOutcome::Agree, "{verdict:?}");
            assert!(verdict.horizon.is_empty());
            assert_eq!(run.mutants[0].report.status, MutantStatus::Survived);
        });
    }

    /// A side that must be explored to an index and is not leaves the slot unknown:
    /// - from 7 the baseline has, at every depth, a path that has appended nothing when the depth
    ///   bound cuts it, so no index of its log is explored on every path; extra's -1 becomes 7,
    ///   and the mutant appends 3 where the baseline only appends 1, but no baseline index is
    ///   complete, so the mutant's prefix is not known to be outside;
    /// - loop's 7 becomes 0: from 0 the mutant also has a path that appends nothing until the
    ///   bound cuts it, so it is explored to no index, and the baseline's prefixes, which every
    ///   mutant path that finishes also has, are not known to be the mutant's.
    #[test]
    fn incomplete_exploration_stays_unknown() {
        on_a_big_stack(|| {
            let validator = choice();
            let from_seven = [test(7)];
            let generation = replaced(validator.baseline(), EXTRA, "-1", "7");
            let seven = run(
                &choosing(&validator, &from_seven, 6),
                &generation,
                finished(),
            );
            let record = record(&seven);
            assert_eq!(
                record.channels[1].complete_to.map(|at| at.elements),
                Some(0)
            );
            let unexplored = verdict(&seven);
            assert_eq!(unexplored.outcome, OracleOutcome::Unknown, "{unexplored:?}");

            let from_zero = [test(0)];
            let generation = replaced(validator.baseline(), "CHOICE.loop", "7", "0");
            let zero = run(
                &choosing(&validator, &from_zero, 6),
                &generation,
                finished(),
            );
            let verdict = verdict(&zero);
            assert_eq!(verdict.outcome, OracleOutcome::Unknown, "{verdict:?}");
            assert!(
                verdict
                    .cause
                    .as_deref()
                    .unwrap_or("")
                    .contains("explored to 0"),
                "{verdict:?}"
            );
        });
    }

    /// `testdata/k/discard.k`, whose `build` puts a partial residue in a cell and whose `clear`
    /// discards it.
    fn discard() -> NativeValidator {
        NativeValidator::bind(
            support::load_path(&Path::new(support::DIR).join("discard.k"), "DISCARD"),
            CompileOptions::default(),
        )
    }

    /// The test `<k> run </k> <n> count </n> <junk> 0 </junk>` of
    /// `discard.k`, whose one slot reads only the end's terminal class and compares crashes, so
    /// that a baseline whose path takes an undefined step is admitted.
    fn discard_test(count: i64) -> TestCase {
        let initial = support::initial_state(support::app("Lblrun", Vec::new()), "SortCmd");
        let Pattern::Application { symbol, arguments } = &initial else {
            unreachable!("a configuration is an application");
        };
        let cell = |name: &str, content: Pattern| {
            support::app(&format!("Lbl'-LT-'{name}'-GT-'"), vec![content])
        };
        TestCase {
            id: format!("discard-{count}"),
            initial_state: Pattern::Application {
                symbol: symbol.clone(),
                arguments: vec![
                    arguments[0].clone(),
                    cell("n", support::int(count)),
                    cell("junk", support::int(0)),
                    arguments[1].clone(),
                ],
            },
            oracles: vec![
                OracleDeclaration::new(
                    CrashPolicy::CompareIdentity,
                    Projection::State(StateProjection::ExitStop {
                        exit_code_cell: None,
                    }),
                )
                .unwrap(),
            ],
        }
    }

    /// The application of `head` in rule `rule`, the only one there, becomes the Int `value`.
    fn application_replaced<'b>(
        baseline: &'b Baseline,
        rule: &str,
        head: &str,
        value: &str,
    ) -> CandidateGeneration<'b> {
        fn walk(b: &Baseline, at: &TermRef, head: &str, out: &mut Vec<TermRef>) {
            let Some(term) = b.term(at) else {
                return;
            };
            if matches!(term.unannotated(), Term::Apply { label, .. } if label.name == head) {
                out.push(at.clone());
            }
            for index in 0.. {
                let mut path = at.path.0.clone();
                path.push(index);
                let child = TermRef::new(at.sentence.clone(), path);
                if b.term(&child).is_none() {
                    break;
                }
                walk(b, &child, head, out);
            }
        }
        let sentence = support::rule(baseline, rule);
        let mut found = Vec::new();
        walk(baseline, &TermRef::new(sentence, [0]), head, &mut found);
        let [at] = found
            .try_into()
            .unwrap_or_else(|found: Vec<_>| panic!("{rule}: {} applications {head}", found.len()));
        let patch = Patch::new(vec![Edit::ReplaceTerm {
            expected: baseline.term(&at).unwrap().clone(),
            at: at.clone(),
            replacement: Term::Token {
                token: value.into(),
                sort: Sort::new("Int"),
            },
        }])
        .unwrap();
        generation(baseline, rule, (at, patch))
    }

    /// Every state of a path whose leaf is real exists, the states before the leaf included: the
    /// definedness of a partial term a step builds stays in the path condition of every later
    /// state of the path, also after a later step discards the term (kink-campaign
    /// `observation`, "Elements, and how a channel ends"). The class `finished` reads `<n>` after
    /// each finish.
    ///
    /// From 20 the baseline's lemma refutes the definedness of `f(20)`, so its one path is an
    /// undefined step at `build`, and its channel is closed by UNDEF with no element.
    /// - The lemma is deleted: the definedness of `f(20)` is open, so the mutant's `build` splits
    ///   into a successor under `⌈f(20)⌉` and an undefined step for the instances where it fails.
    ///   `clear` replaces `f(20)` by 0, so the successor's path holds a ground term of free
    ///   constructors and domain values from there on, and its finish reads 20 where the
    ///   baseline's channel is closed. But that path rests on `f(20)` having a value, and in a
    ///   model of the mutant where it has none the mutant takes the undefined step as the baseline
    ///   does: no kill holds in every pair of models. The state after finish, where the request
    ///   ends at the difference, still holds `⌈f(20)⌉`, which nothing decides, so it is not shown
    ///   to exist and the mutant is `unknown`. Were the obligation dropped with the term, that
    ///   state would be real and the mutant killed.
    /// - build's `f(N)` becomes 0: the same path, through states that exist, reads 20 after
    ///   finish, and the mutant is killed at the channel's element 0.
    #[test]
    fn a_discarded_residue_keeps_its_definedness_on_the_path() {
        on_a_big_stack(|| {
            let validator = discard();
            let options = || {
                observe(
                    vec![PointClass {
                        name: "finished".into(),
                        before: BTreeSet::new(),
                        after: BTreeSet::from(["DISCARD.finish".to_owned()]),
                        cells: vec!["n".into()],
                        stutter: Stutter::Collapse,
                    }],
                    Vec::new(),
                )
            };
            let tests = [discard_test(20)];
            let discarding = Campaign {
                module: "DISCARD",
                ..campaign(&validator, &tests, 8)
            };
            let open = run(
                &discarding,
                &deleted(validator.baseline(), "DISCARD.fceil"),
                options(),
            );
            let Some(Observation::Recorded(record)) = &open.baseline[0].notes.observation else {
                panic!("the baseline records its channels");
            };
            assert!(record.paths.is_none(), "{record:?}");
            assert!(record.channels[0].elements.is_empty(), "{record:?}");
            assert_eq!(
                record.channels[0].end,
                ChannelEnd::Closed(kink_campaign::Closure::Undefined)
            );
            let unshown = verdict(&open);
            assert_eq!(unshown.outcome, OracleOutcome::Unknown, "{unshown:?}");
            assert_eq!(
                unshown.cause.as_deref(),
                Some("the channel `finished` differs at 0 in a state that is not decided"),
            );
            assert_eq!(open.mutants[0].report.status, MutantStatus::Unknown);

            let valued = run(
                &discarding,
                &application_replaced(validator.baseline(), "DISCARD.build", "f", "0"),
                options(),
            );
            assert_eq!(valued.mutants[0].report.status, MutantStatus::Killed);
            let killed = verdict(&valued);
            assert_eq!(
                killed.position,
                position("finished", 0, false),
                "{killed:?}"
            );
            assert_eq!(
                killed.element,
                Some(Element::Content(vec![support::int(20)])),
                "{killed:?}"
            );
        });
    }

    /// `testdata/k/paths.k`, whose runs from `pick` and from `fan` split into paths.
    fn paths() -> NativeValidator {
        NativeValidator::bind(
            support::load_path(&Path::new(support::DIR).join("paths.k"), "PATHS"),
            CompileOptions::default(),
        )
    }

    /// The test `<k> program </k> <n> 0 </n>` of `paths.k`, whose one slot reads only the end's
    /// terminal class.
    fn paths_test(program: &str) -> TestCase {
        let initial = support::initial_state(support::app(program, Vec::new()), "SortCmd");
        let Pattern::Application { symbol, arguments } = &initial else {
            unreachable!("a configuration is an application");
        };
        TestCase {
            id: format!("paths-{program}"),
            initial_state: Pattern::Application {
                symbol: symbol.clone(),
                arguments: vec![
                    arguments[0].clone(),
                    support::app("Lbl'-LT-'n'-GT-'", vec![support::int(0)]),
                    arguments[1].clone(),
                ],
            },
            ..test(0)
        }
    }

    /// The class `picked` (or `seen`), after each of `rules`, with the content `<n>`.
    fn reading_n(name: &str, rules: &[&str]) -> RunOptions {
        observe(
            vec![PointClass {
                name: name.into(),
                before: BTreeSet::new(),
                after: rules.iter().map(|rule| (*rule).to_owned()).collect(),
                cells: vec!["n".into()],
                stutter: Stutter::Collapse,
            }],
            Vec::new(),
        )
    }

    /// From `pick` the paths of `one` and `two` observe 1 and 2 and then reach one configuration
    /// at one depth, `done` with `<n>` 0. The state-set run merges a state only into one whose
    /// path has an equal history, so both are explored, and the baseline's set holds both
    /// prefixes; two's 2 becomes 1, the mutant observes only 1, and the baseline's prefix [2]
    /// kills it. Merged by configuration alone, the second path's prefix would be lost, and the mutant
    /// would agree.
    #[test]
    fn paths_with_different_histories_are_both_kept() {
        on_a_big_stack(|| {
            let validator = paths();
            let tests = [paths_test("Lblpick")];
            let campaign = Campaign {
                module: "PATHS",
                ..campaign(&validator, &tests, 8)
            };
            let generation = replaced(validator.baseline(), "PATHS.two", "2", "1");
            let run = run(
                &campaign,
                &generation,
                reading_n("seen", &["PATHS.one", "PATHS.two"]),
            );
            let record = record(&run);
            assert!(record.real, "{record:?}");
            assert_eq!(record.paths, 2);
            let seen = &record.channels[0];
            assert_eq!(seen.complete_to, None);
            assert_eq!(seen.prefixes[0].len(), 2, "{seen:?}");
            assert_eq!(run.mutants[0].report.status, MutantStatus::Killed);
            assert_eq!(
                verdict(&run).position,
                outside("seen", 0, Outside::Baseline)
            );
        });
    }

    /// A run the work bound cuts while a path is pending: from `fan`, with room for four states,
    /// `low`'s path ends at `done` and `high`'s is cut at its `done`, both explored past their one
    /// element, while `odd`'s path, whose `<n>` would hold `part(3)`, a value no equation gives,
    /// is dropped unexplored. That path bounds the baseline's set at 0, so low's 1 becoming 7,
    /// a prefix outside the explored paths' set, is no kill: the dropped path, whatever `part(3)`
    /// is, may hold it.
    #[test]
    fn a_path_the_work_bound_drops_bounds_the_baseline_set() {
        on_a_big_stack(|| {
            let validator = paths();
            let tests = [paths_test("Lblfan")];
            let campaign = Campaign {
                module: "PATHS",
                ..campaign(&validator, &tests, 8)
            };
            let generation = replaced(validator.baseline(), "PATHS.low", "1", "7");
            let options = RunOptions {
                baseline_max_work: Some(4),
                work: WorkBudget::Calibrated {
                    factor: 0,
                    floor: 100,
                },
                ..reading_n("picked", &["PATHS.low", "PATHS.high", "PATHS.odd"])
            };
            let run = run(&campaign, &generation, options);
            let record = record(&run);
            assert_eq!(record.paths, 3, "{record:?}");
            let picked = &record.channels[0];
            assert_eq!(picked.prefixes[0].len(), 2, "{picked:?}");
            assert_eq!(
                picked.complete_to.map(|at| (at.elements, at.opening)),
                Some((0, kink_campaign::Opening::Bound))
            );
            assert_ne!(run.mutants[0].report.status, MutantStatus::Killed);
            let verdict = verdict(&run);
            assert_eq!(verdict.outcome, OracleOutcome::Unknown, "{verdict:?}");
        });
    }
}
