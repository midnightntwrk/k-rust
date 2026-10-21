//! Rust builders for the execution-pattern rows, replacing the former
//! `execution-pattern-vectors.json`: its terms as KORE patterns, its event pool,
//! its two vocabularies, its nine plans and its side-condition table. The
//! relation-decider rows add a third symbolic address, its events and a three-atom plan.
#![allow(dead_code)]

use k_rust::kore::ast::{Pattern, Sort, Symbol, Variable, VariableKind};
use kink_pattern::{
    Atom, Binding, CollectionEvidence, CollectionStop, Constructor, EvaluationContext,
    EvaluationOptions, Event, EventPresence, EventVocabulary, ExecutionBounds, ExecutionStop,
    ExecutionTerminal, ExecutionTerminalKind, MatchMode, PathInput, PathStop, PatternArm,
    PatternPlan, PayloadClause, Relation, SearchPolicy, SideCondition, SideConditionResult,
    SideConditionRow, SideConditionTable, SymbolSorts, TermRelation,
};

pub fn sort(name: &str) -> Sort {
    Sort::Application {
        name: name.to_owned(),
        arguments: Vec::new(),
    }
}

pub fn app(name: &str, arguments: Vec<Pattern>) -> Pattern {
    Pattern::Application {
        symbol: Symbol {
            name: name.to_owned(),
            sort_parameters: Vec::new(),
        },
        arguments,
    }
}

pub fn int(value: &str) -> Pattern {
    Pattern::DomainValue {
        sort: sort("SortInt"),
        value: value.into(),
    }
}

pub fn var(name: &str, sort_name: &str) -> Pattern {
    Pattern::Variable(Variable {
        kind: VariableKind::Element,
        name: name.to_owned(),
        sort: sort(sort_name),
    })
}

pub fn address(value: &str) -> Pattern {
    app("Lbladdr", vec![int(value)])
}

/// The sort of path predicates in these rows.
fn predicate_sort() -> Sort {
    sort("SortGeneratedTopCell")
}

/// The term pool. `aAlias` is a separately built copy of `a`.
pub fn term(name: &str) -> Pattern {
    match name {
        "a" | "aAlias" => address("1"),
        "b" => address("2"),
        "v7" => int("7"),
        "v8" => int("8"),
        "symbolicA" => var("A0", "SortAddress"),
        "symbolicX" => var("X", "SortAddress"),
        "symbolicY" => var("Y", "SortAddress"),
        "symbolicZ" => var("Z", "SortAddress"),
        other => panic!("no term {other}"),
    }
}

/// Path predicates by name. They are only compared, never decided.
pub fn predicate(name: &str) -> Pattern {
    let equals = || Pattern::Equals {
        operand_sort: Box::new(sort("SortAddress")),
        result_sort: predicate_sort(),
        left: Box::new(term("symbolicX")),
        right: Box::new(term("symbolicY")),
    };
    match name {
        "true" => Pattern::Top {
            sort: predicate_sort(),
        },
        "false" => Pattern::Bottom {
            sort: predicate_sort(),
        },
        "x-equals-y" => equals(),
        "x-not-equals-y" => Pattern::Not {
            sort: predicate_sort(),
            argument: Box::new(equals()),
        },
        other => panic!("no predicate {other}"),
    }
}

pub fn symbol_sorts() -> SymbolSorts {
    SymbolSorts::new([
        (
            "Lbladdr".to_owned(),
            vec![sort("SortInt")],
            sort("SortAddress"),
        ),
        (
            "LblsymbolicAddress".to_owned(),
            vec![sort("SortInt")],
            sort("SortAddress"),
        ),
        ("Lbldone".to_owned(), Vec::new(), sort("SortState")),
        ("Lblstuck".to_owned(), Vec::new(), sort("SortState")),
        ("Lblcrashed".to_owned(), Vec::new(), sort("SortState")),
        ("Lblundefined".to_owned(), Vec::new(), sort("SortState")),
    ])
}

/// Event pool: constructor and payload terms.
fn event_spec(name: &str) -> (&'static str, &'static [&'static str]) {
    match name {
        "x" => ("Other", &[]),
        "wa" => ("memoryWrite", &["a", "v7"]),
        "wb" => ("memoryWrite", &["b", "v8"]),
        "la" => ("memoryLoad", &["a", "v7"]),
        "lAlias" => ("memoryLoad", &["aAlias", "v7"]),
        "lb" => ("memoryLoad", &["b", "v8"]),
        "fa" => ("memoryFree", &["a"]),
        "wSymbolic" => ("memoryWrite", &["symbolicA", "v7"]),
        "lSymbolic" => ("memoryLoad", &["symbolicA", "v8"]),
        "wSymbolicX" => ("memoryWrite", &["symbolicX", "v7"]),
        "lSymbolicY" => ("memoryLoad", &["symbolicY", "v8"]),
        "lSymbolicZ" => ("memoryLoad", &["symbolicZ", "v8"]),
        "fSymbolicZ" => ("memoryFree", &["symbolicZ"]),
        "counterIncrement" => ("counterIncrement", &["v7", "v8"]),
        "branchTaken" => ("branchTaken", &["v8"]),
        other => panic!("no event {other}"),
    }
}

/// Event `name` at `index`, one transition per event.
pub fn event(name: &str, index: usize) -> Event {
    let (constructor, payload) = event_spec(name);
    Event {
        index,
        constructor: constructor.to_owned(),
        payload: payload.iter().map(|name| term(name)).collect(),
        presence: EventPresence::Certain,
        step: u64::try_from(index).expect("small index"),
        emission_ordinal: 0,
    }
}

fn constructor(name: &str, payload: &[&str]) -> Constructor {
    Constructor {
        name: name.to_owned(),
        payload_sorts: payload.iter().map(|name| sort(name)).collect(),
    }
}

pub fn memory_constructors() -> Vec<Constructor> {
    vec![
        constructor("Other", &[]),
        constructor("memoryFree", &["SortAddress"]),
        constructor("memoryLoad", &["SortAddress", "SortInt"]),
        constructor("memoryWrite", &["SortAddress", "SortInt"]),
    ]
}

pub fn counter_constructors() -> Vec<Constructor> {
    vec![
        constructor("branchTaken", &["SortInt"]),
        constructor("counterIncrement", &["SortInt", "SortInt"]),
    ]
}

pub fn memory() -> EventVocabulary {
    EventVocabulary::new(memory_constructors()).expect("memory vocabulary")
}

pub fn counter() -> EventVocabulary {
    EventVocabulary::new(counter_constructors()).expect("counter vocabulary")
}

/// The vocabulary of every observed trace: both families.
pub fn trace_vocabulary() -> EventVocabulary {
    EventVocabulary::new(
        memory_constructors()
            .into_iter()
            .chain(counter_constructors())
            .collect(),
    )
    .expect("trace vocabulary")
}

pub fn bind(position: usize, variable: &str) -> PayloadClause {
    PayloadClause {
        position,
        mode: MatchMode::Bind,
        variable: variable.to_owned(),
    }
}

pub fn use_(position: usize, variable: &str) -> PayloadClause {
    PayloadClause {
        position,
        mode: MatchMode::Use,
        variable: variable.to_owned(),
    }
}

pub fn atom(constructor: &str, payload: Vec<PayloadClause>) -> Atom {
    Atom {
        constructor: constructor.to_owned(),
        payload,
    }
}

/// `memoryWrite(A) <relation> <second>(A)`.
fn write_then(relation: Relation, second: &str) -> PatternArm {
    PatternArm {
        atoms: vec![
            atom("memoryWrite", vec![bind(0, "A")]),
            atom(second, vec![use_(0, "A")]),
        ],
        relations: vec![relation],
    }
}

/// The unvalidated parts of one named plan: vocabulary family, variables, arms, side condition.
pub struct PlanParts {
    pub counter: bool,
    pub variables: Vec<(String, Sort)>,
    pub arms: Vec<PatternArm>,
    pub side_condition: Option<SideCondition>,
}

pub const SIDE_CONDITION: &str = "address-is-valid";

pub fn plan_parts(name: &str) -> PlanParts {
    let address = || vec![("A".to_owned(), sort("SortAddress"))];
    let side = |inputs: &[&str]| {
        Some(SideCondition {
            name: SIDE_CONDITION.to_owned(),
            input_variables: inputs.iter().map(|name| (*name).to_owned()).collect(),
        })
    };
    let (counter, variables, arms, side_condition) = match name {
        "single-write" => (
            false,
            address(),
            vec![PatternArm {
                atoms: vec![atom("memoryWrite", vec![bind(0, "A")])],
                relations: Vec::new(),
            }],
            None,
        ),
        "write-next-load" => (
            false,
            address(),
            vec![write_then(Relation::NextEvent, "memoryLoad")],
            None,
        ),
        "write-eventually-load" => (
            false,
            address(),
            vec![write_then(Relation::EventuallyAfter, "memoryLoad")],
            None,
        ),
        "write-eventually-load-or-free" => (
            false,
            address(),
            vec![
                write_then(Relation::EventuallyAfter, "memoryLoad"),
                write_then(Relation::EventuallyAfter, "memoryFree"),
            ],
            None,
        ),
        "overlapping-load-alternatives" => (
            false,
            address(),
            vec![
                write_then(Relation::EventuallyAfter, "memoryLoad"),
                write_then(Relation::EventuallyAfter, "memoryLoad"),
            ],
            None,
        ),
        "write-eventually-load-eventually-free" => (
            false,
            address(),
            vec![PatternArm {
                atoms: vec![
                    atom("memoryWrite", vec![bind(0, "A")]),
                    atom("memoryLoad", vec![use_(0, "A")]),
                    atom("memoryFree", vec![use_(0, "A")]),
                ],
                relations: vec![Relation::EventuallyAfter, Relation::EventuallyAfter],
            }],
            None,
        ),
        "increment-eventually-branch" => (
            true,
            vec![("N".to_owned(), sort("SortInt"))],
            vec![PatternArm {
                atoms: vec![
                    atom("counterIncrement", vec![bind(1, "N")]),
                    atom("branchTaken", vec![use_(0, "N")]),
                ],
                relations: vec![Relation::EventuallyAfter],
            }],
            None,
        ),
        "write-then-load-side-condition" => (
            false,
            address(),
            vec![write_then(Relation::EventuallyAfter, "memoryLoad")],
            side(&["A"]),
        ),
        "write-then-load-constant-side-condition" => (
            false,
            address(),
            vec![write_then(Relation::EventuallyAfter, "memoryLoad")],
            side(&[]),
        ),
        "nonlexical-subset-side-condition" => (
            false,
            vec![
                ("VALUE".to_owned(), sort("SortInt")),
                ("ADDRESS".to_owned(), sort("SortAddress")),
            ],
            vec![PatternArm {
                atoms: vec![
                    atom("memoryWrite", vec![bind(0, "ADDRESS"), bind(1, "VALUE")]),
                    atom("memoryLoad", vec![use_(0, "ADDRESS"), use_(1, "VALUE")]),
                ],
                relations: vec![Relation::EventuallyAfter],
            }],
            side(&["VALUE"]),
        ),
        other => panic!("no plan {other}"),
    };
    PlanParts {
        counter,
        variables,
        arms,
        side_condition,
    }
}

pub fn plan(name: &str) -> PatternPlan {
    let parts = plan_parts(name);
    let vocabulary = if parts.counter { counter() } else { memory() };
    PatternPlan::new(
        &vocabulary,
        parts.variables,
        parts.arms,
        parts.side_condition,
    )
    .unwrap_or_else(|failure| panic!("{name}: {failure}"))
}

/// Keyed on the named inputs in plan order and the path predicate `true`.
pub fn side_table() -> SideConditionTable {
    let row = |inputs: &[(&str, &str)], result| SideConditionRow {
        condition: SIDE_CONDITION.to_owned(),
        inputs: inputs
            .iter()
            .map(|(name, value)| Binding {
                name: (*name).to_owned(),
                term: term(value),
            })
            .collect(),
        path_predicate: predicate("true"),
        result,
    };
    SideConditionTable::new(vec![
        row(&[], SideConditionResult::True),
        row(&[("VALUE", "v7")], SideConditionResult::True),
        row(&[("A", "a")], SideConditionResult::True),
        row(&[("A", "b")], SideConditionResult::False),
        row(&[("A", "symbolicA")], SideConditionResult::Unknown),
    ])
    .expect("side table")
}

pub fn context(test_id: &str) -> EvaluationContext {
    EvaluationContext {
        test_id: test_id.to_owned(),
        bounds: ExecutionBounds {
            depth: Some(20),
            time_ms: Some(1000),
            branches: Some(8),
            results: Some(8),
        },
        vocabulary: trace_vocabulary(),
        symbol_sorts: symbol_sorts(),
    }
}

pub const fn execution_stop(stop: PathStop) -> ExecutionStop {
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

/// One path of a row. A terminal stop carries a normal terminal, a stuck stop a stuck one.
#[derive(Clone, Copy)]
pub struct PathSpec {
    pub key: Option<&'static str>,
    pub complete: bool,
    pub stop: PathStop,
    pub events: &'static [&'static str],
    pub predicate: &'static str,
    pub equivalences: &'static [(&'static str, &'static str)],
    pub inequalities: &'static [(&'static str, &'static str)],
}

/// A complete, normally terminated path under the predicate `true`.
pub const fn done(key: &'static str, events: &'static [&'static str]) -> PathSpec {
    PathSpec {
        key: Some(key),
        complete: true,
        stop: PathStop::Terminal,
        events,
        predicate: "true",
        equivalences: &[],
        inequalities: &[],
    }
}

/// An incomplete path that stopped at `stop`.
pub const fn stopped(
    key: &'static str,
    stop: PathStop,
    events: &'static [&'static str],
) -> PathSpec {
    PathSpec {
        complete: false,
        stop,
        ..done(key, events)
    }
}

pub fn terminal_state(kind: ExecutionTerminalKind) -> Pattern {
    app(
        match kind {
            ExecutionTerminalKind::Normal => "Lbldone",
            ExecutionTerminalKind::Stuck => "Lblstuck",
            ExecutionTerminalKind::SemanticCrash => "Lblcrashed",
            ExecutionTerminalKind::UndefinedStep => "Lblundefined",
        },
        Vec::new(),
    )
}

pub fn path(spec: &PathSpec, test_id: &str, path_ordinal: usize) -> PathInput {
    let relations = |pairs: &[(&str, &str)]| {
        pairs
            .iter()
            .map(|(left, right)| TermRelation {
                left: term(left),
                right: term(right),
            })
            .collect()
    };
    let execution_stop = execution_stop(spec.stop);
    let execution_terminal = match execution_stop {
        ExecutionStop::Terminal => Some(ExecutionTerminalKind::Normal),
        ExecutionStop::Stuck => Some(ExecutionTerminalKind::Stuck),
        ExecutionStop::UndefinedStep => Some(ExecutionTerminalKind::UndefinedStep),
        _ => None,
    }
    .map(|kind| ExecutionTerminal {
        kind,
        state: terminal_state(kind),
    });
    PathInput {
        test_id: test_id.to_owned(),
        path_ordinal,
        path_key: spec.key.map(str::to_owned),
        complete: spec.complete,
        stop: spec.stop,
        execution_stop,
        execution_terminal,
        events: spec
            .events
            .iter()
            .enumerate()
            .map(|(index, name)| event(name, index))
            .collect(),
        path_predicate: predicate(spec.predicate),
        equivalences: relations(spec.equivalences),
        inequalities: relations(spec.inequalities),
    }
}

pub fn paths(specs: &[PathSpec], test_id: &str) -> Vec<PathInput> {
    specs
        .iter()
        .enumerate()
        .map(|(ordinal, spec)| path(spec, test_id, ordinal))
        .collect()
}

/// Collection evidence as a faithful producer would report it for `paths`.
pub fn collection(paths: &[PathInput], search: SearchPolicy) -> CollectionEvidence {
    let stop = if search == SearchPolicy::ExistentialFirst
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
            .unwrap_or(PathStop::Error)
        {
            PathStop::DepthLimit => CollectionStop::DepthLimit,
            PathStop::TimeLimit => CollectionStop::TimeLimit,
            PathStop::BranchLimit => CollectionStop::BranchLimit,
            PathStop::ResultLimit => CollectionStop::ResultLimit,
            PathStop::ResourceLimit => CollectionStop::ResourceLimit,
            PathStop::SolverUnknown => CollectionStop::SolverUnknown,
            PathStop::BackendLimit => CollectionStop::BackendLimit,
            PathStop::Error => CollectionStop::Error,
            PathStop::MatchFound => CollectionStop::MatchFound,
            PathStop::Terminal | PathStop::Stuck | PathStop::UndefinedStep => {
                CollectionStop::SearchExhausted
            }
        }
    };
    CollectionEvidence {
        stop,
        pending_work: u64::from(stop != CollectionStop::SearchExhausted),
        empty_search_decision: None,
    }
}

pub const fn exhaustive_options() -> EvaluationOptions {
    EvaluationOptions {
        stable_path_keys: true,
        search_policy: SearchPolicy::Exhaustive,
        input_error: false,
    }
}

/// Turns a path into the existential-first match stop.
pub fn make_match_stop(path: &mut PathInput) {
    path.complete = false;
    path.stop = PathStop::MatchFound;
    path.execution_stop = ExecutionStop::QuerySatisfied;
    path.execution_terminal = None;
}
