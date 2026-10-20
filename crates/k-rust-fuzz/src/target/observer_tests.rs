//! Observer targets on real runs (ARCHITECTURE 4.1, 9.2): FZ-FIX's fixtures (`tests/support`)
//! compiled in-process, each case executed through [`Executor::run`], observed through
//! `Backend::execute_observed`, and classed by [`crate::exec::classify`].
//!
//! - COIN `count(N)` steps `count-step` N times, then `count-done` empties `<k>`;
//!   `flip(N)` takes `heads` or `tails` in one step, two paths under all-paths.
//! - RULES `check(7)` ends through `check-miss` and never holds a `count`.
//! - Two COIN programs joined on `<k>` (`count(3) ~> flip(3)`, `flip(3) ~> count(3)`) give a
//!   branch after a shared prefix and paths that continue after the branch.

use std::sync::{
    Arc,
    atomic::{AtomicUsize, Ordering},
};

use k_rust::backend::{CancellationToken, ExecutionLeaf, ObservationEventOutput, ObservedRequest};

use k_rust::kore::ast::Pattern as KorePattern;

use crate::support::{COIN, Compiled, RULES};

use super::{
    ConfigurationView, Observer, ObserverTarget, ObserverVerdict, contains_symbol, walk_paths,
};
use crate::{
    Target, TargetKind,
    assemble::ProgramAssembly,
    error::{CampaignError, TargetProblem},
    exec::{CaseRequestShape, CaseResult, Executor, OutcomeClass},
    spec::{CaseOptions, CompiledDefinition, PathMode},
    target::{Judgement, Resolved, ResolvedTarget},
};

/// A sequence monitor of two events over consecutive configurations: first a step that keeps a
/// `count` on `<k>` (rule `count-step`), then a step that removes it (`count-done`). It accepts
/// at the second event.
struct CountThenDone;

fn k_holds(view: &ConfigurationView, symbol: &str) -> bool {
    view.cell("k")
        .is_some_and(|cell| contains_symbol(cell, symbol))
}

impl Observer for CountThenDone {
    type State = u32;

    fn start(&self) -> u32 {
        0
    }

    fn branch(&self, state: &u32) -> u32 {
        *state
    }

    fn step(
        &self,
        state: &mut u32,
        pre: &ConfigurationView,
        post: &ConfigurationView,
    ) -> ObserverVerdict {
        let counting = k_holds(pre, "Lblcount");
        match *state {
            0 if counting && k_holds(post, "Lblcount") => {
                *state = 1;
                ObserverVerdict::Progress(1)
            }
            1 if counting && !k_holds(post, "Lblcount") => ObserverVerdict::Hit,
            _ => ObserverVerdict::Nothing,
        }
    }
}

/// Accepts a step after which `<out>` holds `wanted`, and counts `branch` calls.
struct OutIs {
    wanted: &'static str,
    branches: Arc<AtomicUsize>,
}

impl Observer for OutIs {
    type State = ();

    fn start(&self) {}

    fn branch(&self, (): &()) {
        self.branches.fetch_add(1, Ordering::SeqCst);
    }

    fn step(
        &self,
        (): &mut (),
        _pre: &ConfigurationView,
        post: &ConfigurationView,
    ) -> ObserverVerdict {
        let holds = post.cell("out").is_some_and(|cell| {
            let mut found = false;
            visit(cell, &mut |pattern| {
                if let KorePattern::DomainValue { value, .. } = pattern {
                    found |= *value == self.wanted;
                }
            });
            found
        });
        if holds {
            ObserverVerdict::Hit
        } else {
            ObserverVerdict::Nothing
        }
    }
}

fn visit(pattern: &KorePattern, each: &mut impl FnMut(&KorePattern)) {
    let mut work = vec![pattern];
    while let Some(next) = work.pop() {
        each(next);
        work.extend(k_rust::kore::walk::children(next));
    }
}

/// Accepts at its first step.
struct FirstStep;

impl Observer for FirstStep {
    type State = ();

    fn start(&self) {}

    fn branch(&self, (): &()) {}

    fn step(
        &self,
        (): &mut (),
        _pre: &ConfigurationView,
        _post: &ConfigurationView,
    ) -> ObserverVerdict {
        ObserverVerdict::Hit
    }
}

fn observer(
    name: &str,
    observer: impl Observer<State: 'static> + Send + Sync + 'static,
    run_to_completion: bool,
) -> Target {
    Target {
        kind: TargetKind::Observer(ObserverTarget::new(name, observer)),
        run_to_completion,
        negated_property: false,
    }
}

/// An observer target with its definition, assembly and executor, as a campaign builds them.
struct Harness {
    compiled: &'static Compiled,
    definition: CompiledDefinition,
    assembly: ProgramAssembly,
    executor: Executor,
    options: CaseOptions,
}

impl Harness {
    fn new(compiled: &'static Compiled, options: CaseOptions) -> Self {
        let definition = compiled.definition();
        let assembly = ProgramAssembly::new(&definition).expect("the definition assembles");
        let executor =
            Executor::new(&definition, &assembly, &options).expect("the executor builds");
        Self {
            compiled,
            definition,
            assembly,
            executor,
            options,
        }
    }

    fn resolve(&mut self, target: &Target) -> Result<ResolvedTarget, CampaignError> {
        ResolvedTarget::resolve(target, &mut self.executor, &self.definition, &self.assembly)
    }

    /// Run the program `file` as written and judge it against `target`.
    fn judge(&mut self, target: &Target, file: &str) -> (CaseResult, Judgement) {
        let resolved = self.resolve(target).expect("the target resolves");
        assert!(resolved.observes());
        let program = self.compiled.fixture.program(file);
        let initial = self
            .compiled
            .assemble(program.file, program.text, program.bindings)
            .unwrap_or_else(|error| panic!("{file} does not assemble: {error}"));
        let shape = CaseRequestShape::new(&self.options, &resolved.needs(self.options.paths));
        let (result, judgement) = resolved
            .run_and_judge(&mut self.executor, &initial, &shape, None)
            .expect("no abort");
        let judgement = judgement.unwrap_or_else(|defect| panic!("{defect:?}: {result:#?}"));
        (result, judgement)
    }
}

fn one_path() -> CaseOptions {
    CaseOptions::default()
}

fn all_paths() -> CaseOptions {
    CaseOptions {
        paths: PathMode::AllPaths,
        ..CaseOptions::default()
    }
}

#[test]
fn a_two_event_observer_accepts_on_one_fixture_and_not_on_another() {
    let target = observer("count-then-done", CountThenDone, false);
    let mut coin = Harness::new(COIN.compiled(), one_path());
    let (result, accepted) = coin.judge(&target, "coin/count.pgm");
    assert_eq!(accepted.class, OutcomeClass::Hit, "{result:#?}");
    assert_eq!(accepted.hit_site, Some(crate::target::HitSite::Leaf(0)));
    // `flip(3)` never holds a `count`: a natural end the observer did not accept.
    let (result, flipped) = coin.judge(&target, "coin/flip.pgm");
    assert_eq!(flipped.class, OutcomeClass::Miss, "{result:#?}");
    assert_eq!(flipped.hit_site, None);
    // Another definition: RULES `check(7)` ends naturally and is not accepted either.
    let mut rules = Harness::new(RULES.compiled(), one_path());
    let (result, checked) = rules.judge(&target, "rules/check.pgm");
    assert_eq!(checked.class, OutcomeClass::Miss, "{result:#?}");
    // The same holds under run-to-completion: the accepting leaf is a natural end.
    let completed = observer("count-then-done", CountThenDone, true);
    let (result, accepted) = coin.judge(&completed, "coin/count.pgm");
    assert_eq!(accepted.class, OutcomeClass::Hit, "{result:#?}");
}

#[test]
fn branch_is_called_for_all_paths_and_the_hit_rests_on_the_accepting_leaf() {
    let branches = Arc::new(AtomicUsize::new(0));
    let out_is = |wanted| {
        observer(
            "out-is",
            OutIs {
                wanted,
                branches: Arc::clone(&branches),
            },
            true,
        )
    };
    let mut coin = Harness::new(COIN.compiled(), all_paths());
    // `flip(3)` ends with `<out>` 3 (`heads`) or 4 (`tails`): one branching point, two children.
    let (result, judgement) = coin.judge(&out_is("4"), "coin/flip.pgm");
    assert_eq!(result.leaves.len(), 2, "{result:#?}");
    assert_eq!(branches.load(Ordering::SeqCst), 2);
    assert_eq!(judgement.class, OutcomeClass::Hit, "{result:#?}");
    let leaf = &result.leaves[match judgement.hit_site {
        Some(crate::target::HitSite::Leaf(index)) => index,
        other => panic!("a hit leaf: {other:?}"),
    }];
    let out = ConfigurationView::new(leaf.state.clone());
    let mut holds_four = false;
    visit(out.cell("out").expect("an <out> cell"), &mut |pattern| {
        if let KorePattern::DomainValue { value, .. } = pattern {
            holds_four |= *value == "4";
        }
    });
    assert!(holds_four, "the hit rests on the `tails` leaf: {leaf:#?}");
    // No end holds 5.
    branches.store(0, Ordering::SeqCst);
    let (result, judgement) = coin.judge(&out_is("5"), "coin/flip.pgm");
    assert_eq!(judgement.class, OutcomeClass::Miss, "{result:#?}");
    assert_eq!(branches.load(Ordering::SeqCst), 2);
    // One path: one leaf, no branching point, no `branch` call.
    branches.store(0, Ordering::SeqCst);
    let mut one = Harness::new(COIN.compiled(), one_path());
    let (result, _) = one.judge(&out_is("4"), "coin/flip.pgm");
    assert_eq!(result.leaves.len(), 1, "{result:#?}");
    assert_eq!(branches.load(Ordering::SeqCst), 0);
}

#[test]
fn an_accepting_leaf_that_is_not_clean_is_no_hit() {
    // `count(3)` needs depth 5 to end; at depth 2 its only leaf is `depth-bound` after the
    // observer accepted on the first step.
    let bounded = CaseOptions {
        max_depth: Some(2),
        ..CaseOptions::default()
    };
    let mut coin = Harness::new(COIN.compiled(), bounded);
    let (result, judgement) = coin.judge(&observer("first", FirstStep, false), "coin/count.pgm");
    assert_eq!(judgement.class, OutcomeClass::Unsupported, "{result:#?}");
    let (result, judgement) = coin.judge(&observer("first", FirstStep, true), "coin/count.pgm");
    assert_eq!(
        judgement.class,
        OutcomeClass::ReachedUnfinished,
        "{result:#?}"
    );
}

#[test]
fn a_target_without_its_observer_is_refused_and_the_observer_is_not_serialized() {
    let target = observer("count-then-done", CountThenDone, false);
    let json = serde_json::to_string(&target).expect("the target serializes");
    assert_eq!(
        json,
        r#"{"kind":{"kind":"observer","name":"count-then-done"},"run-to-completion":false,"negated-property":false}"#
    );
    let read: Target = serde_json::from_str(&json).expect("the target deserializes");
    assert_ne!(read, target, "a read target carries no observer");
    let mut coin = Harness::new(COIN.compiled(), one_path());
    let Err(CampaignError::Target(TargetProblem::Unsupported(message))) = coin.resolve(&read)
    else {
        panic!("a target without its observer must be refused");
    };
    assert!(message.contains("count-then-done"), "{message}");
}

#[test]
fn a_rule_target_is_run_and_judged_by_the_same_entry_point() {
    use super::super::{RuleMode, RuleRef, RuleTarget};
    let target = Target {
        kind: TargetKind::Rule(RuleTarget {
            rule: RuleRef::Label("count-done".to_owned()),
            mode: RuleMode::Fired,
        }),
        run_to_completion: true,
        negated_property: false,
    };
    let mut coin = Harness::new(COIN.compiled(), one_path());
    let resolved = coin.resolve(&target).expect("the rule resolves");
    assert!(!resolved.observes());
    let program = COIN.compiled().fixture.program("coin/count.pgm");
    let initial = COIN
        .compiled()
        .assemble(program.file, program.text, program.bindings)
        .expect("assembles");
    let shape = CaseRequestShape::new(&coin.options, &resolved.needs(coin.options.paths));
    let (_, judgement) = resolved
        .run_and_judge(&mut coin.executor, &initial, &shape, None)
        .expect("no abort");
    assert_eq!(judgement.expect("judged").class, OutcomeClass::Hit);
}

/// Counts `step` and `branch` calls, and accepts nothing.
struct Counting {
    steps: Arc<AtomicUsize>,
    branches: Arc<AtomicUsize>,
}

impl Observer for Counting {
    type State = ();

    fn start(&self) {}

    fn branch(&self, (): &()) {
        self.branches.fetch_add(1, Ordering::SeqCst);
    }

    fn step(
        &self,
        (): &mut (),
        _pre: &ConfigurationView,
        _post: &ConfigurationView,
    ) -> ObserverVerdict {
        self.steps.fetch_add(1, Ordering::SeqCst);
        ObserverVerdict::Nothing
    }
}

/// The contents of the `<k>` cell of `pattern`.
fn k_contents(pattern: &mut KorePattern) -> Option<&mut KorePattern> {
    if let KorePattern::Application { symbol, arguments } = pattern {
        if symbol.name == "Lbl'-LT-'k'-GT-'" {
            return arguments.first_mut();
        }
        for argument in arguments {
            if let Some(found) = k_contents(argument) {
                return Some(found);
            }
        }
    }
    None
}

/// COIN's configuration at depth 0 for the program `file`: the initial configuration with its
/// cells built, which the program's `$PGM` binding alone does not give.
fn configuration(coin: &mut Harness, file: &str) -> KorePattern {
    let options = CaseOptions {
        max_depth: Some(0),
        ..CaseOptions::default()
    };
    let shape = CaseRequestShape::new(&options, &crate::exec::TargetNeeds::default());
    let leaves = coin
        .executor
        .backend_mut()
        .execute(shape.request(COIN.compiled().initial(file)))
        .expect("the run answers")
        .leaves;
    assert_eq!(leaves.len(), 1);
    k_rust::kore::codec::from_value(&leaves[0].state).expect("the state decodes")
}

/// COIN's configuration of `first` with the computation of `second` after it on `<k>`:
/// `first ~> second`.
fn joined(coin: &mut Harness, first: &str, second: &str) -> KorePattern {
    let mut initial = configuration(coin, first);
    let mut other = configuration(coin, second);
    let rest = k_contents(&mut other).expect("a <k> cell").clone();
    let Some(KorePattern::Application { symbol, arguments }) = k_contents(&mut initial) else {
        panic!("<k> holds a sequence: {initial}");
    };
    assert_eq!(symbol.name, "kseq", "<k> holds a sequence");
    arguments[1] = rest;
    initial
}

/// Run `initial` under all paths through `execute_observed` with every event, as the observer
/// target's re-run does, and return its leaves.
fn observed_leaves(coin: &mut Harness, initial: KorePattern) -> Vec<ExecutionLeaf> {
    let shape = CaseRequestShape::new(&coin.options, &crate::exec::TargetNeeds::default());
    coin.executor
        .backend_mut()
        .execute_observed(ObservedRequest {
            request: shape.request(initial),
            rules: None,
        })
        .expect("the observed run answers")
        .leaves
}

#[test]
fn a_branch_after_a_shared_prefix_is_shown_once_per_committed_transition() {
    let steps = Arc::new(AtomicUsize::new(0));
    let branches = Arc::new(AtomicUsize::new(0));
    let counting = Counting {
        steps: Arc::clone(&steps),
        branches: Arc::clone(&branches),
    };
    let mut coin = Harness::new(COIN.compiled(), all_paths());
    // `count(3) ~> flip(3)`: three `count-step`s and a `count-done` shared by both paths, then
    // `heads` or `tails`.
    let leaves = {
        let initial = joined(&mut coin, "coin/count.pgm", "coin/flip.pgm");
        observed_leaves(&mut coin, initial)
    };
    assert_eq!(leaves.len(), 2);
    assert_eq!(leaves[0].branch.len(), 5);
    assert_eq!(leaves[0].branch[..4], leaves[1].branch[..4]);
    let paths = walk_paths(&counting, &leaves);
    assert!(!paths.unobservable);
    assert_eq!(paths.reached, [false, false]);
    // Six distinct committed transitions, one branching point with two successors.
    assert_eq!(steps.load(Ordering::SeqCst), 6);
    assert_eq!(branches.load(Ordering::SeqCst), 2);
    // A two-event monitor sees the shared prefix on both paths.
    let paths = walk_paths(&CountThenDone, &leaves);
    assert_eq!(paths.reached, [true, true]);
}

#[test]
fn an_unobservable_sibling_keeps_the_branching_and_is_never_a_miss() {
    let mut coin = Harness::new(COIN.compiled(), all_paths());
    // `flip(3) ~> count(3)`: `heads` or `tails`, then the `count-step`s and `count-done` on each
    // path, whose configurations only that path's events carry.
    let mut leaves = {
        let initial = joined(&mut coin, "coin/flip.pgm", "coin/count.pgm");
        observed_leaves(&mut coin, initial)
    };
    assert_eq!(leaves.len(), 2);
    let first_rule = |leaf: &ExecutionLeaf| {
        leaf.observations
            .iter()
            .find_map(|event| match event {
                ObservationEventOutput::Transition { rule_label, .. } => rule_label.clone(),
                _ => None,
            })
            .expect("a labelled first step")
    };
    let hidden_tails = first_rule(&leaves[1]).contains("tails");
    let (hidden, shown) = if hidden_tails { ("4", "3") } else { ("3", "4") };
    // As if the filter had dropped the events of leaf 1's path.
    leaves[1].observations.clear();
    let branches = Arc::new(AtomicUsize::new(0));
    let out_is = |wanted| OutIs {
        wanted,
        branches: Arc::clone(&branches),
    };
    // Accepting on the hidden path: nothing is reached, and the walk says so.
    let paths = walk_paths(&out_is(hidden), &leaves);
    assert_eq!(paths.reached, [false, false]);
    assert!(paths.unobservable);
    // The branching point is the run's: both successors get their `branch` call.
    assert_eq!(branches.load(Ordering::SeqCst), 2);
    // Accepting on the shown path still reaches its leaf.
    let paths = walk_paths(&out_is(shown), &leaves);
    assert_eq!(paths.reached, [true, false]);
    assert!(paths.unobservable);
}

#[test]
fn a_cancelled_case_is_a_timeout_and_no_defect() {
    let target = observer("count-then-done", CountThenDone, false);
    let mut coin = Harness::new(COIN.compiled(), one_path());
    let resolved = coin.resolve(&target).expect("the target resolves");
    let program = COIN.compiled().fixture.program("coin/count.pgm");
    let initial = COIN
        .compiled()
        .assemble(program.file, program.text, program.bindings)
        .expect("assembles");
    let shape = CaseRequestShape::new(&coin.options, &resolved.needs(coin.options.paths));
    let token = CancellationToken::new();
    token.cancel();
    let (result, judgement) = resolved
        .run_and_judge(&mut coin.executor, &initial, &shape, Some(&token))
        .expect("no abort");
    let judgement = judgement.unwrap_or_else(|defect| panic!("{defect:?}: {result:#?}"));
    assert_eq!(judgement.class, OutcomeClass::Timeout, "{result:#?}");
    assert_eq!(judgement.hit_site, None);
}

#[test]
fn the_observation_filter_keeps_rewrite_rules_only_and_a_blank_name_is_refused() {
    let mut coin = Harness::new(COIN.compiled(), one_path());
    let resolved = coin
        .resolve(&observer("count-then-done", CountThenDone, false))
        .expect("the target resolves");
    let Resolved::Observer { rules: Some(rules) } = &resolved.resolved else {
        panic!("COIN accepts the rewrite-rule filter");
    };
    assert_eq!(rules.len(), 4, "{rules:?}");
    let Err(CampaignError::Target(TargetProblem::Unsupported(message))) =
        coin.resolve(&observer(" ", CountThenDone, false))
    else {
        panic!("a blank observer name must be refused");
    };
    assert!(message.contains("name"), "{message}");
}

#[test]
fn the_observed_re_run_is_charged_to_the_case() {
    let target = observer("count-then-done", CountThenDone, false);
    let mut coin = Harness::new(COIN.compiled(), one_path());
    let resolved = coin.resolve(&target).expect("the target resolves");
    let program = COIN.compiled().fixture.program("coin/count.pgm");
    let initial = COIN
        .compiled()
        .assemble(program.file, program.text, program.bindings)
        .expect("assembles");
    let shape = CaseRequestShape::new(&coin.options, &resolved.needs(coin.options.paths));
    let plain = coin
        .executor
        .run(&initial, &shape, &[], None)
        .expect("no abort");
    let (observed, _) = resolved
        .run_and_judge(&mut coin.executor, &initial, &shape, None)
        .expect("no abort");
    assert!(plain.work > 0);
    assert_eq!(observed.work, 2 * plain.work);
}
