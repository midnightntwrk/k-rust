//! Corpus-scale CS-04 (README 4.6): the incremental monitor and the shared-prefix tree
//! evaluator, checked against `evaluate_with` over exhaustive synthetic traces and trees.
//!
//! The differential compares the whole `Result<Evaluation, PatternFailure>`: outcome, every
//! witness (path, arm, indices, events, bindings, assumptions, predicate, stops), the primary
//! witness, `complete_coverage`, `failure`, policy and bounds, and every error.

use std::collections::BTreeMap;

use k_rust::kore::ast::{Pattern, Sort, Variable, VariableKind};
use kink_pattern::{
    Atom, CollectionEvidence, CollectionStop, Constructor, Evaluation, EvaluationContext,
    EvaluationOptions, Event, EventPresence, EventVocabulary, ExecutionBounds, ExecutionStop,
    ExecutionTerminal, ExecutionTerminalKind, Feasibility, MatchMode, Monitor, MonitorError,
    MonitorOptions, PathInput, PathStop, PathTree, PatternArm, PatternFailure, PatternFailureKind,
    PatternOutcome, PatternPlan, PayloadClause, Relation, RelationDecider, RelationDecision,
    SearchPolicy, SideCondition, SideConditionResult, SideConditionRow, SideConditionTable,
    StructuralDecider, SymbolSorts, TermRelation, TreeError, TreeOptions, evaluate_tree,
    evaluate_tree_with_stats, evaluate_with,
};

// ---------------------------------------------------------------- terms, events, paths

fn sort(name: &str) -> Sort {
    Sort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

fn int(value: &str) -> Pattern {
    Pattern::DomainValue {
        sort: sort("SortInt"),
        value: value.into(),
    }
}

fn y() -> Pattern {
    Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: "Y".to_owned(),
        sort: sort("SortInt"),
    })
}

fn relation(left: Pattern, right: Pattern) -> TermRelation {
    TermRelation { left, right }
}

fn y_is(value: &str) -> TermRelation {
    relation(y(), int(value))
}

/// The two path predicates: `\top`, and `not (Y = 1)`, under which the scripted decider
/// refutes `Y = 1`.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Predicate {
    Top,
    NotY1,
}

fn predicate(predicate: Predicate) -> Pattern {
    let cell = sort("SortGeneratedTopCell");
    match predicate {
        Predicate::Top => Pattern::Top { sort: cell },
        Predicate::NotY1 => Pattern::Not {
            sort: cell.clone(),
            argument: Box::new(Pattern::Equals {
                operand_sort: Box::new(sort("SortInt")),
                result_sort: cell,
                left: Box::new(y()),
                right: Box::new(int("1")),
            }),
        },
    }
}

fn vocabulary() -> EventVocabulary {
    EventVocabulary::new(vec![
        Constructor {
            name: "a".into(),
            payload_sorts: vec![sort("SortInt")],
        },
        Constructor {
            name: "b".into(),
            payload_sorts: vec![sort("SortInt")],
        },
        Constructor {
            name: "c".into(),
            payload_sorts: Vec::new(),
        },
    ])
    .expect("vocabulary")
}

/// The event alphabet: every constructor under every presence, ground and symbolic payloads.
const ALPHABET: [&str; 10] = ["a1", "a2", "aY", "aC", "aU", "b1", "bY", "bU", "c", "cC"];
/// Two reduced alphabets for the long traces.
const LONG_ONE: [&str; 4] = ["a1", "aC", "bY", "c"];
const LONG_TWO: [&str; 4] = ["aY", "aU", "b1", "cC"];

fn event(name: &str, index: usize, width: usize) -> Event {
    let (constructor, payload, presence) = match name {
        "a1" => ("a", vec![int("1")], EventPresence::Certain),
        "a2" => ("a", vec![int("2")], EventPresence::Certain),
        "aY" => ("a", vec![y()], EventPresence::Certain),
        "aC" => (
            "a",
            vec![int("1")],
            EventPresence::Conditional(vec![y_is("1")]),
        ),
        "aU" => ("a", Vec::new(), EventPresence::Undecided),
        "b1" => ("b", vec![int("1")], EventPresence::Certain),
        "bY" => ("b", vec![y()], EventPresence::Conditional(vec![y_is("2")])),
        "bU" => ("b", Vec::new(), EventPresence::Undecided),
        "c" => ("c", Vec::new(), EventPresence::Certain),
        "cC" => ("c", Vec::new(), EventPresence::Conditional(vec![y_is("1")])),
        other => panic!("no event {other}"),
    };
    Event {
        index,
        constructor: constructor.into(),
        payload,
        presence,
        step: u64::try_from(index / width).expect("small"),
        emission_ordinal: u64::try_from(index % width).expect("small"),
    }
}

fn events(names: &[&str], width: usize) -> Vec<Event> {
    names
        .iter()
        .enumerate()
        .map(|(index, name)| event(name, index, width))
        .collect()
}

const fn execution_stop(stop: PathStop) -> ExecutionStop {
    match stop {
        PathStop::Terminal => ExecutionStop::Terminal,
        PathStop::Stuck => ExecutionStop::Stuck,
        PathStop::UndefinedStep => ExecutionStop::UndefinedStep,
        PathStop::MatchFound => ExecutionStop::QuerySatisfied,
        PathStop::DepthLimit => ExecutionStop::DepthLimit,
        PathStop::TimeLimit => ExecutionStop::TimeLimit,
        PathStop::BranchLimit => ExecutionStop::BranchLimit,
        PathStop::ResultLimit => ExecutionStop::ResultLimit,
        PathStop::ResourceLimit => ExecutionStop::ResourceLimit,
        PathStop::SolverUnknown => ExecutionStop::SolverUnknown,
        PathStop::BackendLimit => ExecutionStop::BackendLimit,
        PathStop::Error => ExecutionStop::Error,
    }
}

/// How one leaf ends.
#[derive(Clone, Copy, Debug)]
struct Leaf {
    stop: PathStop,
    predicate: Predicate,
}

const DONE: Leaf = Leaf {
    stop: PathStop::Terminal,
    predicate: Predicate::Top,
};
const CUT: Leaf = Leaf {
    stop: PathStop::DepthLimit,
    predicate: Predicate::Top,
};
const OPAQUE: Leaf = Leaf {
    stop: PathStop::BackendLimit,
    predicate: Predicate::Top,
};
const NEGATED: Leaf = Leaf {
    stop: PathStop::Terminal,
    predicate: Predicate::NotY1,
};

fn path(ordinal: usize, keyed: bool, events: Vec<Event>, leaf: Leaf) -> PathInput {
    let complete = leaf.stop.is_complete();
    let terminal = match leaf.stop {
        PathStop::Terminal => Some(ExecutionTerminalKind::Normal),
        PathStop::Stuck => Some(ExecutionTerminalKind::Stuck),
        PathStop::UndefinedStep => Some(ExecutionTerminalKind::UndefinedStep),
        _ => None,
    };
    PathInput {
        test_id: "t".into(),
        path_ordinal: ordinal,
        path_key: keyed.then(|| format!("leaf:{ordinal}")),
        complete,
        stop: leaf.stop,
        execution_stop: execution_stop(leaf.stop),
        execution_terminal: terminal.map(|kind| ExecutionTerminal {
            kind,
            state: int("0"),
        }),
        events,
        path_predicate: predicate(leaf.predicate),
        equivalences: Vec::new(),
        inequalities: Vec::new(),
    }
}

fn context() -> EvaluationContext {
    EvaluationContext {
        test_id: "t".into(),
        bounds: ExecutionBounds {
            depth: Some(8),
            time_ms: Some(1000),
            branches: Some(8),
            results: Some(8),
        },
        vocabulary: vocabulary(),
        symbol_sorts: SymbolSorts::default(),
    }
}

/// Collection evidence as a faithful producer reports it.
fn collection(paths: &[PathInput], policy: SearchPolicy) -> CollectionEvidence {
    let stop = if policy == SearchPolicy::ExistentialFirst
        && paths.iter().any(|path| path.stop == PathStop::MatchFound)
    {
        CollectionStop::MatchFound
    } else if paths.iter().all(|path| path.complete) {
        CollectionStop::SearchExhausted
    } else {
        match paths
            .iter()
            .find(|path| !path.complete)
            .map(|path| path.stop)
        {
            Some(PathStop::DepthLimit) => CollectionStop::DepthLimit,
            Some(PathStop::BackendLimit) => CollectionStop::BackendLimit,
            _ => CollectionStop::Error,
        }
    };
    CollectionEvidence {
        stop,
        pending_work: u64::from(stop != CollectionStop::SearchExhausted),
        empty_search_decision: None,
    }
}

const fn options(keyed: bool, policy: SearchPolicy) -> EvaluationOptions {
    EvaluationOptions {
        stable_path_keys: keyed,
        search_policy: policy,
        input_error: false,
    }
}

const EXHAUSTIVE: EvaluationOptions = options(true, SearchPolicy::Exhaustive);

// ---------------------------------------------------------------- plans

fn bind(position: usize, variable: &str) -> PayloadClause {
    PayloadClause {
        position,
        mode: MatchMode::Bind,
        variable: variable.into(),
    }
}

fn use_(position: usize, variable: &str) -> PayloadClause {
    PayloadClause {
        position,
        mode: MatchMode::Use,
        variable: variable.into(),
    }
}

fn atom(constructor: &str, payload: Vec<PayloadClause>) -> Atom {
    Atom {
        constructor: constructor.into(),
        payload,
    }
}

fn arm(atoms: Vec<Atom>, relations: Vec<Relation>) -> PatternArm {
    PatternArm { atoms, relations }
}

fn int_variables(names: &[&str]) -> Vec<(String, Sort)> {
    names
        .iter()
        .map(|name| ((*name).to_owned(), sort("SortInt")))
        .collect()
}

/// Presence x relation x Bind/Use, one to three atoms, one or two arms.
fn plans() -> Vec<(&'static str, PatternPlan)> {
    use Relation::{EventuallyAfter as Ev, NextEvent as Next};
    let vocabulary = vocabulary();
    let plan = |variables: &[&str], arms: Vec<PatternArm>| {
        PatternPlan::new(&vocabulary, int_variables(variables), arms, None).expect("plan")
    };
    vec![
        (
            "a(X)",
            plan(
                &["X"],
                vec![arm(vec![atom("a", vec![bind(0, "X")])], vec![])],
            ),
        ),
        ("c", plan(&[], vec![arm(vec![atom("c", vec![])], vec![])])),
        (
            "a(X) next b(X)",
            plan(
                &["X"],
                vec![arm(
                    vec![atom("a", vec![bind(0, "X")]), atom("b", vec![use_(0, "X")])],
                    vec![Next],
                )],
            ),
        ),
        (
            "a(X) eventually b(X)",
            plan(
                &["X"],
                vec![arm(
                    vec![atom("a", vec![bind(0, "X")]), atom("b", vec![use_(0, "X")])],
                    vec![Ev],
                )],
            ),
        ),
        (
            "a(X) next a(X)",
            plan(
                &["X"],
                vec![arm(
                    vec![atom("a", vec![bind(0, "X")]), atom("a", vec![use_(0, "X")])],
                    vec![Next],
                )],
            ),
        ),
        (
            "a(X) eventually a(X)",
            plan(
                &["X"],
                vec![arm(
                    vec![atom("a", vec![bind(0, "X")]), atom("a", vec![use_(0, "X")])],
                    vec![Ev],
                )],
            ),
        ),
        (
            "c next c",
            plan(
                &[],
                vec![arm(vec![atom("c", vec![]), atom("c", vec![])], vec![Next])],
            ),
        ),
        (
            "c eventually c eventually c",
            plan(
                &[],
                vec![arm(
                    vec![atom("c", vec![]), atom("c", vec![]), atom("c", vec![])],
                    vec![Ev, Ev],
                )],
            ),
        ),
        (
            "a(X) eventually c next b(X)",
            plan(
                &["X"],
                vec![arm(
                    vec![
                        atom("a", vec![bind(0, "X")]),
                        atom("c", vec![]),
                        atom("b", vec![use_(0, "X")]),
                    ],
                    vec![Ev, Next],
                )],
            ),
        ),
        (
            "a(X) next c next a(X)",
            plan(
                &["X"],
                vec![arm(
                    vec![
                        atom("a", vec![bind(0, "X")]),
                        atom("c", vec![]),
                        atom("a", vec![use_(0, "X")]),
                    ],
                    vec![Next, Next],
                )],
            ),
        ),
        (
            "a(X) next b(X) | b(X) eventually a(X)",
            plan(
                &["X"],
                vec![
                    arm(
                        vec![atom("a", vec![bind(0, "X")]), atom("b", vec![use_(0, "X")])],
                        vec![Next],
                    ),
                    arm(
                        vec![atom("b", vec![bind(0, "X")]), atom("a", vec![use_(0, "X")])],
                        vec![Ev],
                    ),
                ],
            ),
        ),
        (
            "a(X) eventually b(Z)",
            plan(
                &["X", "Z"],
                vec![arm(
                    vec![atom("a", vec![bind(0, "X")]), atom("b", vec![bind(0, "Z")])],
                    vec![Ev],
                )],
            ),
        ),
    ]
}

// ---------------------------------------------------------------- deciders

/// A pure scripted decider over `Y` and ground integers. `relate` depends on the path only
/// through its predicate: under `not (Y = 1)` it refutes `Y = 1`. `feasible` refutes
/// conflicting values of `Y` and cannot decide `Y = 2`, nor `Y = 1` under `not (Y = 1)` (so
/// a relation decided under the wrong predicate shows as a different outcome).
struct Scripted;

fn y_values(assumptions: &[TermRelation]) -> Vec<Pattern> {
    assumptions
        .iter()
        .filter(|relation| relation.left == y())
        .map(|relation| relation.right.clone())
        .collect()
}

impl RelationDecider for Scripted {
    fn relate(
        &self,
        path: &PathInput,
        assumed: &[TermRelation],
        left: &Pattern,
        right: &Pattern,
    ) -> RelationDecision {
        if left == right {
            return RelationDecision::Equal;
        }
        let (symbolic, ground) = match (left == &y(), right == &y()) {
            (true, false) => (true, right),
            (false, true) => (true, left),
            _ => (false, right),
        };
        if !symbolic {
            return RelationDecision::Unequal;
        }
        if path.path_predicate == predicate(Predicate::NotY1) && ground == &int("1") {
            return RelationDecision::Unequal;
        }
        let known = y_values(assumed);
        if known.iter().any(|value| value != ground) {
            RelationDecision::Unequal
        } else if known.contains(ground) {
            RelationDecision::Equal
        } else {
            RelationDecision::EqualIf(vec![relation(y(), ground.clone())])
        }
    }

    fn feasible(&self, path: &PathInput, assumptions: &[TermRelation]) -> Feasibility {
        let values = y_values(assumptions);
        if values.windows(2).any(|pair| pair[0] != pair[1]) {
            Feasibility::Unsat
        } else if values.contains(&int("2"))
            || (path.path_predicate == predicate(Predicate::NotY1) && values.contains(&int("1")))
        {
            Feasibility::Unknown
        } else {
            Feasibility::Sat
        }
    }
}

/// Decides nothing.
struct Opaque;

impl RelationDecider for Opaque {
    fn relate(
        &self,
        _path: &PathInput,
        _assumed: &[TermRelation],
        left: &Pattern,
        right: &Pattern,
    ) -> RelationDecision {
        if left == right {
            RelationDecision::Equal
        } else {
            RelationDecision::Indeterminate
        }
    }

    fn feasible(&self, _path: &PathInput, assumptions: &[TermRelation]) -> Feasibility {
        if assumptions.is_empty() {
            Feasibility::Sat
        } else {
            Feasibility::Unknown
        }
    }
}

fn deciders() -> [(&'static str, &'static dyn RelationDecider); 3] {
    [
        ("structural", &StructuralDecider),
        ("scripted", &Scripted),
        ("opaque", &Opaque),
    ]
}

// ---------------------------------------------------------------- comparison

const fn tree_options(evaluation: EvaluationOptions) -> TreeOptions {
    TreeOptions {
        evaluation,
        monitor: MonitorOptions { cap: 4096 },
    }
}

/// Counts of what the compared evaluations covered, so the suite cannot pass vacuously.
#[derive(Debug, Default)]
struct Tally {
    compared: usize,
    outcomes: BTreeMap<String, usize>,
    with_assumptions: usize,
    errors: usize,
}

impl Tally {
    fn record(&mut self, result: &Result<Evaluation, PatternFailure>) {
        self.compared += 1;
        match result {
            Ok(evaluation) => {
                *self
                    .outcomes
                    .entry(format!("{:?}", evaluation.outcome))
                    .or_default() += 1;
                if evaluation
                    .witnesses
                    .iter()
                    .any(|witness| !witness.assumptions.is_empty())
                {
                    self.with_assumptions += 1;
                }
            }
            Err(_) => self.errors += 1,
        }
    }

    fn assert_covers_every_outcome(&self) {
        for outcome in ["Match", "NoMatch", "Unknown"] {
            assert!(
                self.outcomes.get(outcome).copied().unwrap_or(0) > 0,
                "{outcome} never occurred: {self:?}"
            );
        }
        assert!(
            self.with_assumptions > 0,
            "no conditional witness: {self:?}"
        );
    }
}

/// Compares the tree evaluation with `evaluate_with` over the tree's leaves.
fn compare(
    label: &str,
    plan: &PatternPlan,
    tree: &PathTree,
    evaluation: EvaluationOptions,
    decider: &dyn RelationDecider,
    tally: &mut Tally,
) {
    let context = context();
    let collection = collection(tree.paths(), evaluation.search_policy);
    let reference = evaluate_with(
        &context,
        plan,
        tree.paths(),
        &collection,
        None,
        evaluation,
        decider,
    );
    let monitored = evaluate_tree_with_stats(
        &context,
        plan,
        tree,
        &collection,
        None,
        tree_options(evaluation),
        decider,
    );
    // The monitor computes every honest result itself: it returns the reference's own result
    // only where the reference fails its existential-first collection check.
    let deferred = monitored.as_ref().is_ok_and(|(_, stats)| stats.deferred);
    assert!(!deferred || reference.is_err(), "{label}: deferred");
    assert_eq!(
        monitored.map(|(evaluation, _)| evaluation),
        reference,
        "{label}"
    );
    tally.record(&reference);
}

fn words<'a>(alphabet: &[&'a str], length: usize) -> Vec<Vec<&'a str>> {
    let mut words = vec![Vec::new()];
    for _ in 0..length {
        words = words
            .into_iter()
            .flat_map(|word| {
                alphabet.iter().map(move |letter| {
                    let mut next = word.clone();
                    next.push(*letter);
                    next
                })
            })
            .collect();
    }
    words
}

// ---------------------------------------------------------------- differential: single paths

/// Every trace of length 0..=3 over the full alphabet, every plan, every decider, under four
/// leaf ends (complete, depth cut, no real prefix, complete under `not (Y = 1)`).
#[test]
fn single_paths_up_to_three_events_agree_with_evaluate_with() {
    let plans = plans();
    let mut tally = Tally::default();
    for length in 0..=3 {
        for word in words(&ALPHABET, length) {
            for leaf in [DONE, CUT, OPAQUE, NEGATED] {
                let tree = PathTree::from_paths(vec![path(0, true, events(&word, 1), leaf)]);
                for (plan_name, plan) in &plans {
                    for (decider_name, decider) in deciders() {
                        compare(
                            &format!("{word:?} {leaf:?} {plan_name} {decider_name}"),
                            plan,
                            &tree,
                            EXHAUSTIVE,
                            decider,
                            &mut tally,
                        );
                    }
                }
            }
        }
    }
    eprintln!("CS04 single-path rows (length <= 3): {tally:?}");
    tally.assert_covers_every_outcome();
}

/// Every trace of length 4..=6 over two reduced alphabets (one event per step, and two events
/// per step), every plan, the scripted decider.
#[test]
fn single_paths_of_four_to_six_events_agree_with_evaluate_with() {
    let plans = plans();
    let mut tally = Tally::default();
    for alphabet in [LONG_ONE, LONG_TWO] {
        for length in 4..=6 {
            for word in words(&alphabet, length) {
                for width in [1, 2] {
                    let tree =
                        PathTree::from_paths(vec![path(0, true, events(&word, width), DONE)]);
                    for (plan_name, plan) in &plans {
                        compare(
                            &format!("{word:?} width {width} {plan_name}"),
                            plan,
                            &tree,
                            EXHAUSTIVE,
                            &Scripted,
                            &mut tally,
                        );
                    }
                }
            }
        }
    }
    eprintln!("CS04 single-path rows (length 4..=6): {tally:?}");
    tally.assert_covers_every_outcome();
}

// ---------------------------------------------------------------- differential: trees

/// One branch below a shared prefix: its own events, and how its leaf ends (`None`: the
/// branch is discarded and has no leaf).
type Branch<'a> = (&'a [&'a str], Option<Leaf>);

/// A tree built node by node: the prefix as one node per event, then each branch below it.
fn tree_of(prefix: &[&str], branches: &[Branch<'_>], keyed: bool) -> PathTree {
    let mut tree = PathTree::new();
    let mut node = PathTree::ROOT;
    for (index, name) in prefix.iter().enumerate() {
        node = tree
            .add_child(node, vec![event(name, index, 1)])
            .expect("node");
    }
    let mut ordinal = 0;
    for (suffix, leaf) in branches {
        let mut current = node;
        let mut names = prefix.to_vec();
        for name in *suffix {
            current = tree
                .add_child(current, vec![event(name, names.len(), 1)])
                .expect("node");
            names.push(name);
        }
        if let Some(leaf) = leaf {
            tree.add_leaf(current, path(ordinal, keyed, events(&names, 1), *leaf))
                .expect("leaf events equal the node chain");
            ordinal += 1;
        }
    }
    tree
}

/// The branch sets below every prefix: sibling leaves with different events, a leaf at the
/// branch point itself, a discarded sibling, an indeterminate candidate only on a discarded
/// branch, sibling leaves under different predicates, a sibling without a real prefix, and
/// twin leaves (which unkeyed mode must refuse).
fn branch_sets() -> Vec<Vec<Branch<'static>>> {
    vec![
        vec![(&["b1"], Some(DONE)), (&["bY"], Some(DONE))],
        vec![(&["b1"], Some(DONE)), (&["b1"], Some(NEGATED))],
        vec![(&["bY"], Some(DONE)), (&["bY"], Some(NEGATED))],
        vec![(&[], Some(CUT)), (&["b1"], Some(DONE))],
        vec![(&["b1"], Some(DONE)), (&["bU"], None)],
        vec![(&["bU"], Some(DONE)), (&["b1"], Some(DONE)), (&["c"], None)],
        vec![(&["c", "b1"], Some(DONE)), (&["cC", "bY"], Some(OPAQUE))],
        vec![(&["a1"], Some(CUT)), (&["aU", "b1"], Some(DONE))],
        vec![(&["c"], Some(DONE)), (&["c", "a2"], Some(NEGATED))],
        vec![(&[], None), (&["aY", "b1"], Some(DONE)), (&["b1"], None)],
        vec![(&["b1"], Some(DONE)), (&["b1"], Some(DONE))],
    ]
}

/// Every prefix of length 0..=2 over the full alphabet below every branch set, keyed and
/// unkeyed, every plan, the scripted and structural deciders.
#[test]
fn trees_with_shared_prefixes_agree_with_evaluate_with() {
    let plans = plans();
    let mut tally = Tally::default();
    for length in 0..=2 {
        for prefix in words(&ALPHABET, length) {
            for branches in branch_sets() {
                for keyed in [true, false] {
                    let tree = tree_of(&prefix, &branches, keyed);
                    let evaluation = options(keyed, SearchPolicy::Exhaustive);
                    for (plan_name, plan) in &plans {
                        for (decider_name, decider) in &deciders()[..2] {
                            compare(
                                &format!(
                                    "{prefix:?} {branches:?} keyed {keyed} {plan_name} {decider_name}"
                                ),
                                plan,
                                &tree,
                                evaluation,
                                *decider,
                                &mut tally,
                            );
                        }
                    }
                }
            }
        }
    }
    eprintln!("CS04 tree rows: {tally:?}");
    tally.assert_covers_every_outcome();
    assert!(tally.errors > 0, "unkeyed duplicate shapes must be refused");
}

/// `PathTree::from_paths` shares the prefixes of equal step events; its evaluation equals the
/// node-by-node tree's and `evaluate_with`'s, with one and two events per step.
#[test]
fn trees_from_paths_share_prefixes_and_agree() {
    let plans = plans();
    let mut tally = Tally::default();
    for prefix in words(&LONG_ONE, 2).into_iter().chain(words(&LONG_TWO, 2)) {
        for branches in branch_sets() {
            let built = tree_of(&prefix, &branches, true);
            for width in [1, 2] {
                let leaves = built
                    .paths()
                    .iter()
                    .map(|leaf| {
                        let mut leaf = leaf.clone();
                        for event in &mut leaf.events {
                            event.step = u64::try_from(event.index / width).expect("small");
                            event.emission_ordinal =
                                u64::try_from(event.index % width).expect("small");
                        }
                        leaf
                    })
                    .collect::<Vec<_>>();
                let shared = PathTree::from_paths(leaves);
                assert!(
                    shared.nodes() <= built.nodes(),
                    "from_paths shares prefixes"
                );
                for (plan_name, plan) in &plans {
                    compare(
                        &format!("{prefix:?} {branches:?} width {width} {plan_name}"),
                        plan,
                        &shared,
                        EXHAUSTIVE,
                        &Scripted,
                        &mut tally,
                    );
                }
            }
        }
    }
    eprintln!("CS04 from_paths rows: {tally:?}");
    tally.assert_covers_every_outcome();
}

// ---------------------------------------------------------------- named rows

fn plan_named(name: &str) -> PatternPlan {
    plans()
        .into_iter()
        .find(|(plan_name, _)| *plan_name == name)
        .map(|(_, plan)| plan)
        .expect("named plan")
}

fn evaluate_both(
    plan: &PatternPlan,
    tree: &PathTree,
    monitor: MonitorOptions,
    decider: &dyn RelationDecider,
) -> (
    Result<Evaluation, PatternFailure>,
    Result<Evaluation, PatternFailure>,
) {
    let context = context();
    let collection = collection(tree.paths(), SearchPolicy::Exhaustive);
    (
        evaluate_tree(
            &context,
            plan,
            tree,
            &collection,
            None,
            TreeOptions {
                evaluation: EXHAUSTIVE,
                monitor,
            },
            decider,
        ),
        evaluate_with(
            &context,
            plan,
            tree.paths(),
            &collection,
            None,
            EXHAUSTIVE,
            decider,
        ),
    )
}

/// C5: a cap overflow is never silent. `a(X) eventually b(X)` over `a(1) a(2) a(1)` with no
/// `b` is NoMatch with complete coverage; with a cap of one partial the monitor evicts and
/// reports Unknown, never NoMatch or Match.
#[test]
fn cap_overflow_is_unknown_where_evaluate_with_is_no_match() {
    let plan = plan_named("a(X) eventually b(X)");
    let tree = PathTree::from_paths(vec![path(0, true, events(&["a1", "a2", "a1"], 1), DONE)]);
    let (monitored, reference) =
        evaluate_both(&plan, &tree, MonitorOptions::default(), &StructuralDecider);
    assert_eq!(monitored, reference);
    let reference = reference.expect("evaluation");
    assert_eq!(reference.outcome, PatternOutcome::NoMatch);
    assert!(reference.complete_coverage);

    let context = context();
    let collection = collection(tree.paths(), SearchPolicy::Exhaustive);
    let (capped, stats) = evaluate_tree_with_stats(
        &context,
        &plan,
        &tree,
        &collection,
        None,
        TreeOptions {
            evaluation: EXHAUSTIVE,
            monitor: MonitorOptions { cap: 1 },
        },
        &StructuralDecider,
    )
    .expect("evaluation");
    assert!(stats.overflowed);
    assert_eq!(capped.outcome, PatternOutcome::Unknown);
    assert!(!capped.complete_coverage);
    assert_eq!(capped.failure, Some(PathStop::SolverUnknown));
}

/// The cap only removes evidence: over every short single path, with caps 0, 1 and 2, the
/// capped witnesses are a subset of the reference's, NoMatch only where the reference is
/// NoMatch, and an overflow never leaves NoMatch.
#[test]
fn a_cap_never_creates_a_witness_or_a_no_match() {
    let plans = plans();
    let context = context();
    let mut overflows = 0;
    for length in 0..=3 {
        for word in words(&ALPHABET, length) {
            let tree = PathTree::from_paths(vec![path(0, true, events(&word, 1), DONE)]);
            let collection = collection(tree.paths(), SearchPolicy::Exhaustive);
            for (plan_name, plan) in &plans {
                let reference = evaluate_with(
                    &context,
                    plan,
                    tree.paths(),
                    &collection,
                    None,
                    EXHAUSTIVE,
                    &Scripted,
                )
                .expect("reference");
                for cap in 0..=2 {
                    let (capped, stats) = evaluate_tree_with_stats(
                        &context,
                        plan,
                        &tree,
                        &collection,
                        None,
                        TreeOptions {
                            evaluation: EXHAUSTIVE,
                            monitor: MonitorOptions { cap },
                        },
                        &Scripted,
                    )
                    .expect("capped");
                    let label = format!("{word:?} {plan_name} cap {cap}");
                    assert!(
                        capped
                            .witnesses
                            .iter()
                            .all(|witness| reference.witnesses.contains(witness)),
                        "{label}"
                    );
                    if capped.outcome == PatternOutcome::NoMatch {
                        assert_eq!(reference.outcome, PatternOutcome::NoMatch, "{label}");
                    }
                    if stats.overflowed {
                        overflows += 1;
                        assert_ne!(capped.outcome, PatternOutcome::NoMatch, "{label}");
                    } else {
                        assert_eq!(capped, reference, "{label}");
                    }
                }
            }
        }
    }
    assert!(overflows > 0);
}

/// The T1 rule: two leaves with equal events below a shared prefix but different predicates
/// are evaluated under their own predicates. Under `not (Y = 1)` the scripted decider refutes
/// `a(Y)` against `b(1)`, so the plan matches only on the `\top` leaf, and the two leaves are
/// separate groups.
#[test]
fn leaf_predicate_dependent_relations_are_decided_per_leaf() {
    let plan = plan_named("a(X) eventually b(X)");
    let tree = tree_of(
        &["aY"],
        &[(&["b1"], Some(DONE)), (&["b1"], Some(NEGATED))],
        true,
    );
    let (monitored, reference) = evaluate_both(&plan, &tree, MonitorOptions::default(), &Scripted);
    assert_eq!(monitored, reference);
    let reference = reference.expect("evaluation");
    assert_eq!(reference.outcome, PatternOutcome::Match);
    assert_eq!(reference.witnesses.len(), 1);
    assert_eq!(reference.witnesses[0].path_key.as_deref(), Some("leaf:0"));
    assert_eq!(reference.witnesses[0].assumptions, vec![y_is("1")]);

    let context = context();
    let collection = collection(tree.paths(), SearchPolicy::Exhaustive);
    let (_, stats) = evaluate_tree_with_stats(
        &context,
        &plan,
        &tree,
        &collection,
        None,
        tree_options(EXHAUSTIVE),
        &Scripted,
    )
    .expect("evaluation");
    assert_eq!(stats.groups, 2);

    // Equal predicates share one group and visit the shared prefix once.
    let shared = tree_of(
        &["aY"],
        &[(&["b1"], Some(DONE)), (&["bY"], Some(DONE))],
        true,
    );
    let (_, stats) = evaluate_tree_with_stats(
        &context,
        &plan,
        &shared,
        &collection,
        None,
        tree_options(EXHAUSTIVE),
        &Scripted,
    )
    .expect("evaluation");
    assert_eq!(stats.groups, 1);
    assert_eq!(stats.node_visits, 4, "root, prefix, two branches");
}

/// An indeterminate candidate on a shared prefix counts for every kept leaf below it; one only
/// on a discarded branch counts for none.
#[test]
fn indeterminate_candidates_follow_kept_leaves_only() {
    let plan = plan_named("a(X) eventually b(X)");
    // `aU` on the prefix: every kept leaf is indeterminate.
    let on_prefix = tree_of(&["aU"], &[(&["b1"], Some(DONE)), (&["c"], None)], true);
    let (monitored, reference) =
        evaluate_both(&plan, &on_prefix, MonitorOptions::default(), &Scripted);
    assert_eq!(monitored, reference);
    assert_eq!(
        reference.expect("evaluation").outcome,
        PatternOutcome::Unknown
    );
    // `bU` only on the discarded branch: the kept leaf decides.
    let discarded = tree_of(&["a1"], &[(&["b1"], Some(DONE)), (&["bU"], None)], true);
    let (monitored, reference) =
        evaluate_both(&plan, &discarded, MonitorOptions::default(), &Scripted);
    assert_eq!(monitored, reference);
    assert_eq!(
        reference.expect("evaluation").outcome,
        PatternOutcome::Match
    );
    let no_match = tree_of(&["a1"], &[(&["c"], Some(DONE)), (&["bU"], None)], true);
    let (monitored, reference) =
        evaluate_both(&plan, &no_match, MonitorOptions::default(), &Scripted);
    assert_eq!(monitored, reference);
    assert_eq!(
        reference.expect("evaluation").outcome,
        PatternOutcome::NoMatch
    );
}

/// The `NextEvent` gap across a branch point: a Certain event ends the scan, a non-Certain one
/// leaves only an indeterminate candidate, on either side of the branch.
#[test]
fn next_event_gaps_across_a_branch_point() {
    let plan = plan_named("a(X) next b(X)");
    for (branches, expected) in [
        (
            vec![(&["c", "b1"][..], Some(DONE))],
            PatternOutcome::NoMatch,
        ),
        (
            vec![(&["cC", "b1"][..], Some(DONE))],
            PatternOutcome::Unknown,
        ),
        (vec![(&["b1"][..], Some(DONE))], PatternOutcome::Match),
    ] {
        let tree = tree_of(&["a1"], &branches, true);
        let (monitored, reference) =
            evaluate_both(&plan, &tree, MonitorOptions::default(), &Scripted);
        assert_eq!(monitored, reference, "{branches:?}");
        assert_eq!(
            reference.expect("evaluation").outcome,
            expected,
            "{branches:?}"
        );
    }
    // A Certain *matching* event at the gap position also ends the scan of the earlier
    // partial: `a(1) a(1) b(1)` under `a(X) next b(X)` has the one witness [1, 2].
    let tree = PathTree::from_paths(vec![path(0, true, events(&["a1", "a1", "b1"], 1), DONE)]);
    let (monitored, reference) = evaluate_both(&plan, &tree, MonitorOptions::default(), &Scripted);
    assert_eq!(monitored, reference);
    let reference = reference.expect("evaluation");
    assert_eq!(reference.outcome, PatternOutcome::Match);
    assert_eq!(reference.witnesses.len(), 1);
    assert_eq!(reference.witnesses[0].event_indices, vec![1, 2]);
}

/// Two occurrences with equal bindings and assumptions are two witnesses: the chosen event
/// indices are part of a partial's key.
#[test]
fn occurrences_with_equal_bindings_are_distinct_witnesses() {
    let plan = plan_named("a(X) eventually b(X)");
    let tree = PathTree::from_paths(vec![path(0, true, events(&["a1", "a1", "b1"], 1), DONE)]);
    let (monitored, reference) = evaluate_both(&plan, &tree, MonitorOptions::default(), &Scripted);
    assert_eq!(monitored, reference);
    let indices = reference
        .expect("evaluation")
        .witnesses
        .into_iter()
        .map(|witness| witness.event_indices)
        .collect::<Vec<_>>();
    assert_eq!(indices, vec![vec![0, 2], vec![1, 2]]);
}

/// R(k): the incremental monitor, read after k events under the depth-k cut, gives exactly
/// the witnesses `evaluate_with` gives for the k-prefix as a leaf; read under a complete
/// k-prefix, its indeterminate flag is exactly the reference's Unknown.
#[test]
fn incremental_reads_equal_the_batch_evaluation_of_every_prefix() {
    let plans = plans();
    let context = context();
    for alphabet in [LONG_ONE, LONG_TWO] {
        for word in words(&alphabet, 5) {
            let all = events(&word, 1);
            for (plan_name, plan) in &plans {
                let mut monitor = Monitor::new(plan, MonitorOptions::default());
                for k in 0..=all.len() {
                    if k > 0 {
                        let relate_on = path(0, true, all[..k].to_vec(), DONE);
                        monitor
                            .push_step(&all[k - 1..k], &relate_on, &Scripted)
                            .expect("push");
                    }
                    for leaf in [CUT, DONE] {
                        let cut = path(0, true, all[..k].to_vec(), leaf);
                        let reference = evaluate_with(
                            &context,
                            plan,
                            std::slice::from_ref(&cut),
                            &collection(std::slice::from_ref(&cut), SearchPolicy::Exhaustive),
                            None,
                            EXHAUSTIVE,
                            &Scripted,
                        )
                        .expect("reference");
                        let mut verdict = monitor.finish(&cut, &Scripted).expect("finish");
                        verdict.witnesses.sort_by(|left, right| {
                            left.event_indices
                                .cmp(&right.event_indices)
                                .then_with(|| left.bindings.cmp(&right.bindings))
                                .then_with(|| left.assumptions.cmp(&right.assumptions))
                                .then_with(|| left.arm_ordinal.cmp(&right.arm_ordinal))
                        });
                        let label = format!("{word:?} k {k} {leaf:?} {plan_name}");
                        assert_eq!(verdict.witnesses, reference.witnesses, "{label}");
                        if leaf.stop.is_complete() && verdict.witnesses.is_empty() {
                            assert_eq!(
                                verdict.indeterminate,
                                reference.outcome == PatternOutcome::Unknown,
                                "{label}"
                            );
                        }
                    }
                }
            }
        }
    }
}

/// C6: a branch is a copy; what one child sees never reaches its sibling or its parent.
#[test]
fn branches_are_copies_and_never_merge() {
    let plan = plan_named("a(X) eventually b(X)");
    let prefix = events(&["a1"], 1);
    let relate_on = path(0, true, prefix.clone(), DONE);
    let mut parent = Monitor::new(&plan, MonitorOptions::default());
    parent
        .push_step(&prefix, &relate_on, &Scripted)
        .expect("push");
    let mut left = parent.branch();
    let mut right = parent.branch();
    let left_events = events(&["a1", "b1"], 1);
    let right_events = events(&["a1", "aU"], 1);
    left.push_step(&left_events[1..], &relate_on, &Scripted)
        .expect("push");
    right
        .push_step(&right_events[1..], &relate_on, &Scripted)
        .expect("push");
    let left_verdict = left
        .finish(&path(0, true, left_events, DONE), &Scripted)
        .expect("finish");
    let right_verdict = right
        .finish(&path(0, true, right_events, DONE), &Scripted)
        .expect("finish");
    assert_eq!(left_verdict.witnesses.len(), 1);
    assert!(!left_verdict.indeterminate);
    assert!(right_verdict.witnesses.is_empty());
    assert!(right_verdict.indeterminate);
    assert_eq!(parent.events(), 1);
    assert_eq!(parent.partials(), 1);
    assert!(!parent.indeterminate());

    // An indeterminate candidate before the branch point is inherited by every child.
    let undecided = events(&["aU", "b1"], 1);
    let relate_on = path(0, true, undecided.clone(), DONE);
    let mut parent = Monitor::new(&plan, MonitorOptions::default());
    parent
        .push_step(&undecided[..1], &relate_on, &Scripted)
        .expect("push");
    assert!(parent.indeterminate());
    let mut child = parent.branch();
    assert!(child.indeterminate());
    child
        .push_step(&undecided[1..], &relate_on, &Scripted)
        .expect("push");
    assert!(
        child
            .finish(&relate_on, &Scripted)
            .expect("finish")
            .indeterminate
    );
}

/// The per-leaf `indeterminate` flag reaches the match-found leaf below a branch point: an
/// existential-first stop whose only candidate lies on the shared prefix is honest.
#[test]
fn match_found_leaf_inherits_the_prefix_candidate() {
    let plan = plan_named("a(X) eventually b(X)");
    let stop = Leaf {
        stop: PathStop::MatchFound,
        predicate: Predicate::Top,
    };
    let tree = tree_of(&["aU"], &[(&["c"], Some(stop)), (&["b1"], Some(CUT))], true);
    let mut tally = Tally::default();
    compare(
        "match-found leaf below an undecided prefix",
        &plan,
        &tree,
        options(true, SearchPolicy::ExistentialFirst),
        &Scripted,
        &mut tally,
    );
    assert_eq!(tally.outcomes.get("Unknown"), Some(&1));
}

/// The incremental API refuses events out of order and a path with other events.
#[test]
fn incremental_api_misuse_is_refused() {
    let plan = plan_named("a(X)");
    let all = events(&["a1", "b1"], 1);
    let relate_on = path(0, true, all.clone(), DONE);
    let mut monitor = Monitor::new(&plan, MonitorOptions::default());
    assert_eq!(
        monitor.push_step(&all[1..], &relate_on, &Scripted),
        Err(MonitorError::EventIndex {
            expected: 0,
            found: 1
        })
    );
    monitor
        .push_step(&all[..1], &relate_on, &Scripted)
        .expect("push");
    assert_eq!(
        monitor.finish(&relate_on, &Scripted),
        Err(MonitorError::PathEvents { pushed: 1, path: 2 })
    );
    let mut tree = PathTree::new();
    assert_eq!(
        tree.add_child(7, Vec::new()),
        Err(TreeError::UnknownNode(7))
    );
    let node = tree
        .add_child(PathTree::ROOT, all[..1].to_vec())
        .expect("node");
    assert_eq!(
        tree.add_leaf(node, relate_on),
        Err(TreeError::LeafEvents { node })
    );
}

/// Existential-first collections: an honest match-found path agrees; a match-found path
/// without its witness and a witness off the match-found path are the reference's own errors.
#[test]
fn existential_first_agrees_and_dishonest_stops_are_the_reference_errors() {
    let plans = plans();
    let first = options(true, SearchPolicy::ExistentialFirst);
    let stop = Leaf {
        stop: PathStop::MatchFound,
        predicate: Predicate::Top,
    };
    let mut tally = Tally::default();
    for length in 0..=3 {
        for word in words(&LONG_ONE, length) {
            for others in [vec![], vec![CUT], vec![DONE]] {
                let mut leaves = vec![path(0, true, events(&word, 1), stop)];
                for (offset, leaf) in others.iter().enumerate() {
                    leaves.push(path(offset + 1, true, events(&["a1", "b1"], 1), *leaf));
                }
                let tree = PathTree::from_paths(leaves);
                for (plan_name, plan) in &plans {
                    compare(
                        &format!("{word:?} {others:?} {plan_name}"),
                        plan,
                        &tree,
                        first,
                        &Scripted,
                        &mut tally,
                    );
                }
            }
        }
    }
    eprintln!("CS04 existential-first rows: {tally:?}");
    assert!(tally.errors > 0);
    assert!(tally.outcomes.get("Match").copied().unwrap_or(0) > 0);
}

/// Every validation error is `evaluate_with`'s own.
#[test]
fn invalid_inputs_fail_exactly_as_evaluate_with() {
    let plan = plan_named("a(X) eventually b(X)");
    let context = context();
    let good = || path(0, true, events(&["a1", "b1"], 1), DONE);
    let mut cases: Vec<(&str, Vec<PathInput>, CollectionEvidence, EvaluationOptions)> = Vec::new();
    let exhausted = CollectionEvidence {
        stop: CollectionStop::SearchExhausted,
        pending_work: 0,
        empty_search_decision: None,
    };
    let mut other_test = good();
    other_test.test_id = "other".into();
    cases.push((
        "test mismatch",
        vec![other_test],
        exhausted.clone(),
        EXHAUSTIVE,
    ));
    let mut duplicate = good();
    duplicate.path_ordinal = 0;
    cases.push((
        "duplicate ordinal",
        vec![good(), duplicate],
        exhausted.clone(),
        EXHAUSTIVE,
    ));
    let mut unkeyed = good();
    unkeyed.path_key = None;
    cases.push((
        "unkeyed in keyed mode",
        vec![unkeyed.clone()],
        exhausted.clone(),
        EXHAUSTIVE,
    ));
    let mut twin = unkeyed.clone();
    twin.path_ordinal = 1;
    cases.push((
        "unkeyed twins",
        vec![unkeyed, twin],
        exhausted.clone(),
        options(false, SearchPolicy::Exhaustive),
    ));
    let mut bad_index = good();
    bad_index.events[1].index = 5;
    cases.push((
        "event index",
        vec![bad_index],
        exhausted.clone(),
        EXHAUSTIVE,
    ));
    let mut bad_terminal = good();
    bad_terminal.execution_terminal = None;
    cases.push((
        "terminal mismatch",
        vec![bad_terminal],
        exhausted.clone(),
        EXHAUSTIVE,
    ));
    let mut bad_payload = good();
    bad_payload.events[0].payload.clear();
    cases.push((
        "payload arity",
        vec![bad_payload],
        exhausted.clone(),
        EXHAUSTIVE,
    ));
    cases.push((
        "pending work",
        vec![good()],
        CollectionEvidence {
            pending_work: 1,
            ..exhausted.clone()
        },
        EXHAUSTIVE,
    ));
    cases.push((
        "empty exhaustion without decision",
        vec![],
        exhausted.clone(),
        EXHAUSTIVE,
    ));
    for (label, paths, collection, evaluation) in cases {
        let tree = PathTree::from_paths(paths);
        let reference = evaluate_with(
            &context,
            &plan,
            tree.paths(),
            &collection,
            None,
            evaluation,
            &Scripted,
        );
        assert!(reference.is_err(), "{label} must be refused");
        let monitored = evaluate_tree(
            &context,
            &plan,
            &tree,
            &collection,
            None,
            tree_options(evaluation),
            &Scripted,
        );
        assert_eq!(monitored, reference, "{label}");
    }

    // A plan built against another declaration of `a`: the vocabulary mismatch is detected
    // through the plan's own vocabulary.
    let other = EventVocabulary::new(vec![Constructor {
        name: "a".into(),
        payload_sorts: vec![sort("SortBool")],
    }])
    .expect("vocabulary");
    let mismatched = PatternPlan::new(
        &other,
        Vec::new(),
        vec![arm(vec![atom("a", vec![])], vec![])],
        None,
    )
    .expect("plan");
    let tree = PathTree::from_paths(vec![good()]);
    let reference = evaluate_with(
        &context,
        &mismatched,
        tree.paths(),
        &exhausted,
        None,
        EXHAUSTIVE,
        &Scripted,
    );
    assert_eq!(
        reference.as_ref().map_err(PatternFailure::kind),
        Err(PatternFailureKind::VocabularyMismatch)
    );
    assert_eq!(
        evaluate_tree(
            &context,
            &mismatched,
            &tree,
            &exhausted,
            None,
            tree_options(EXHAUSTIVE),
            &Scripted
        ),
        reference
    );

    // An input error is the reference's error evaluation.
    let errored = EvaluationOptions {
        input_error: true,
        ..EXHAUSTIVE
    };
    assert_eq!(
        evaluate_tree(
            &context,
            &plan,
            &tree,
            &exhausted,
            None,
            tree_options(errored),
            &Scripted
        ),
        evaluate_with(
            &context,
            &plan,
            tree.paths(),
            &exhausted,
            None,
            errored,
            &Scripted
        )
    );
}

/// Side conditions: without a table every occurrence is indeterminate, as in the reference;
/// with a table the tree evaluator returns the reference's result (the rows are private to
/// it) and says so.
#[test]
fn side_conditions_are_unknown_without_a_table_and_deferred_with_one() {
    let vocabulary = vocabulary();
    let plan = PatternPlan::new(
        &vocabulary,
        int_variables(&["X"]),
        vec![arm(
            vec![atom("a", vec![bind(0, "X")]), atom("b", vec![use_(0, "X")])],
            vec![Relation::EventuallyAfter],
        )],
        Some(SideCondition {
            name: "positive".into(),
            input_variables: vec!["X".into()],
        }),
    )
    .expect("plan");
    let context = context();
    let tree = PathTree::from_paths(vec![path(0, true, events(&["a1", "b1"], 1), DONE)]);
    let exhausted = collection(tree.paths(), SearchPolicy::Exhaustive);
    let (monitored, reference) = evaluate_both(&plan, &tree, MonitorOptions::default(), &Scripted);
    assert_eq!(monitored, reference);
    assert_eq!(
        reference.expect("evaluation").outcome,
        PatternOutcome::Unknown
    );
    let table = SideConditionTable::new(vec![SideConditionRow {
        condition: "positive".into(),
        inputs: vec![kink_pattern::Binding {
            name: "X".into(),
            term: int("1"),
        }],
        path_predicate: predicate(Predicate::Top),
        result: SideConditionResult::True,
    }])
    .expect("table");
    let (monitored, stats) = evaluate_tree_with_stats(
        &context,
        &plan,
        &tree,
        &exhausted,
        Some(&table),
        tree_options(EXHAUSTIVE),
        &Scripted,
    )
    .expect("evaluation");
    assert!(stats.deferred);
    assert_eq!(monitored.outcome, PatternOutcome::Match);
    assert_eq!(
        Ok(monitored),
        evaluate_with(
            &context,
            &plan,
            tree.paths(),
            &exhausted,
            Some(&table),
            EXHAUSTIVE,
            &Scripted
        )
    );
}
