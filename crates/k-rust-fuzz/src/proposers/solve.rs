//! The solve proposer: symbolic execution from a partly concrete start, then a model query for
//! the holes a blocking guard depends on (ARCHITECTURE 8.6). Owner: FZ-15. Native builds with
//! the `z3` feature only.
//!
//! # Why
//!
//! The climb (`super::climb`) walks a hole towards a guard by its branch distance, which needs a
//! slope. A guard such as `H *Int I ==Int 2021027 andBool 1 <Int H andBool H <Int I` has none:
//! with one hole fixed the distance is least where the other is `2021027 / I`, and zero only
//! when `I` divides `2021027`. A solver answers it directly: the guard is a formula over the
//! holes, and a model of it is an assignment that passes it.
//!
//! # When it runs
//!
//! The proposer watches every case (`Proposer::observe_all`). It keeps the best score any case
//! reached (`crate::score`) and counts the cases since the score last improved; a run of
//! [`SOLVE_STALL_CASES`] cases without a better score is a stall (when the climb runs, a stall
//! of the climb). A *blocked case* is a `miss` that entered and refuted the `requires` of a rule
//! on the target's keyed chain: the target itself, its direct predecessors whose right-hand side
//! keys the head of `<k>`, theirs, and so on up to
//! [`SOLVE_CHAIN_RADIUS`](crate::report::SOLVE_CHAIN_RADIUS) edges (where a rule has no keyed
//! predecessor, all its predecessors; `crate::score::RuleScorer::with_chain`). A case's blocked
//! rule is its refuted chain entry of least (chain distance, guard distance)
//! (`RuleScorer::blocked`), and the cases of a solving campaign record the condition entries of
//! every chain rule.
//!
//! Every blocked case gives a query ([`Query::key`]: the rule, the symbolic holes, the other
//! holes' values). The proposer keeps the unsettled queries, one per key, each with the rank of
//! the best blocked case that asks it, at most [`SOLVE_PENDING_LIMIT`] (dropping the
//! worst-ranked). On a stall it is ready with the pending query of least rank (the first
//! observed of equal ones), and the schedule draws it by its weight within its share of the
//! budget. An asked query is settled, whatever it answered, and leaves the pending set, so a
//! query that found no candidate (no path, no model, a candidate that missed) gives way to the
//! next one at the next draw, with the stall still running; a run a cancellation or the
//! per-case safety limit stopped is settled too, and charged at least 1 work. A blocked rule and set of
//! symbolic holes whose queries found no candidate [`SOLVE_FUTILE_LIMIT`] times (with other
//! values of the other holes) is given up for the campaign: on the maze's unreachable `u4` the
//! queries differ only in holes no guard on the path reads, and without the limit a campaign of
//! 5000 cases asked about 1000 of them, each ~30 ms of backend construction and solving for one
//! state's work. Other rules, other symbolic sets and other blocked cases stay available. A candidate that passes a
//! chain rule's guard gives a blocked case one rule nearer the target, so on a corridor of guards
//! the proposer solves them one by one.
//!
//! # Which holes are symbolic
//!
//! Only the holes on which the blocking condition depends are made symbolic (ARCHITECTURE 8.6,
//! R-25); the others keep the blocked case's values. The condition records (`collectConditions`,
//! G-7) bind the condition's variables to the values the matched instance gave them, and each
//! atom names the bindings it reads; a hole whose value reaches a rule unchanged is among those
//! bindings (input-to-state correspondence, as the climb uses). So a hole is symbolic when its
//! sort is `Int` or `Bool` (the sorts that translate exactly to SMT, G-11), it has more than one
//! admissible value (a one-value choice set is fixed), and its value in the blocked case is one
//! of the values the condition's atoms read ([`symbolic_holes`]). A hole whose value reaches the
//! guard only through a computation is not found this way and stays concrete; two holes with
//! the same value are both made symbolic when the guard reads that value.
//!
//! # The query
//!
//! The blocked case's configuration is assembled as any case's is, and each symbolic hole's
//! value at its position (`crate::holes::RoundTripCheck::positions`; for a KORE-template hole,
//! its variable) is replaced by a fresh variable `VarKrustFuzzHole<n>` of its sort. Each symbolic
//! hole's declared constraints (`range`, `choices`) are conjoined to the state. The state runs on
//! a backend of the proposer's own, built for this query from the campaign's internalized
//! definition, under strategy `all`, with traces, within a work bound of [`SOLVE_WORK_FACTOR`]
//! times the blocked case's work plus [`SOLVE_WORK_SLACK`] states and the case options' depth
//! bound (the depth budget: about the blocked case's own path, with room for the branches the
//! symbolic holes open). The blocked rule is not a terminal rule: the backend stops at a
//! terminal rule only on a step with a single successor, and a symbolic hole makes the blocked
//! rule's step branch. Instead, every leaf whose path applied the blocked rule (its trace has the
//! rule's `rewrite` entry, established: not the last entry of a `work-bound`, `timeout` or
//! `cancelled` leaf) carries the path condition and the rule's condition in its constraint. For
//! each such leaf, up to [`SOLVE_MAX_MODEL_QUERIES`], `Backend::get_model` asks for a model of
//! its constraint; the first satisfiable one gives the symbolic holes' values
//! ([`model_values`]), and a hole the model leaves free keeps its value (a model that gives no
//! symbolic hole a value is a failed run, not the blocked case again).
//!
//! Both backends use the clock-free solver mode (`BackendOptions::smt_resource_limit`): each
//! decision of the run gets [`SOLVE_RUN_RESOURCE_UNITS`] Z3 resource units with
//! [`SOLVE_RUN_RETRIES`] retries at doubled units, and an undecided one is handled as the backend
//! handles any undecided answer (an indeterminate step, or both sides kept); each model query
//! gets [`SOLVE_MODEL_RESOURCE_UNITS`] with [`SOLVE_MODEL_RETRIES`] retries, and an undecided one
//! gives no candidate. The budgets were measured on the maze's `c7`: with this Z3 both its rule
//! condition and its model are decided only at a third attempt on the thread, whatever the
//! units of the first two (a single attempt of 100,000,000 units leaves them undecided; three
//! of 100,000, 200,000 and 400,000 decide the condition), so two retries at small units cost
//! least; a decision that stays undecided costs 1,750,000 units in the run, about 0.1 s.
//! Z3 counts the units in its own search, so these answers do not depend on the machine's speed
//! or load (the budgets and the Z3 version are in `identity.solve`).
//!
//! # Candidates
//!
//! A model is a candidate, never a witness: its values must be admissible for their holes
//! (`values::admissible`: sort, constraints, generation bounds), and the candidate then runs as
//! an ordinary case through the round-trip check, the concrete execution and, on a hit, the
//! confirmation on a fresh backend (ARCHITECTURE 7). Under strategy `any` the concrete run may
//! take another rule than the symbolic path did; the candidate then misses, and nothing is
//! claimed.
//!
//! # Budget
//!
//! The proposer spends at most [`SOLVE_BUDGET_SHARE`] of the campaign's cases and of its work,
//! as the climb does with its half (`engine::schedule`). Its work is that of its candidate cases
//! plus that of its symbolic runs: each run is charged the states it visited (its `work`) and 1
//! per model query, to the proposer's share and to the campaign's `totals.work`, before its
//! candidate runs. A candidate case runs even when the run spent the rest of a work budget, so
//! a work budget may be exceeded by one run's bound plus one case's work. The report counts the
//! runs and their outcomes (`report::SolveTotals`).
//!
//! # Determinism
//!
//! Each query runs on a thread of its own with backends of its own, so no solver state is
//! shared with the cases, with the confirmations or with earlier queries: Z3's context is per
//! thread in this build (finding Z3-THREAD-CONTEXT), and the backend's cache of decided answers
//! is per backend. With the clock-free budgets every answer of a query, `unknown` included, is
//! then a function of the query, the budgets and the Z3 version, so a solving campaign's report
//! is a function of the same inputs as any campaign's plus the Z3 version (ARCHITECTURE 5.4).
//! What stays outside: a run with a stack stop, and one a cancellation or the per-case safety
//! limit stopped (`SolveTotals::outside_determinism`); and the cases themselves, which run
//! under the case options' clocked solver as in every campaign, with their own `smtUnknowns`
//! exclusion.

use std::{
    collections::{BTreeMap, BTreeSet},
    num::NonZeroU32,
    thread,
    time::{Duration, Instant},
};

use k_rust::{
    backend::{
        Backend, BackendOptions, CancellationToken, CancelledResultOutput, ExecuteRequest,
        ExecutionLeaf, ExecutionStrategy, HaltReasonOutput, PatternRequest, ResultModalityOutput,
    },
    k_rust_backend::definition::BackendDefinition,
    kore::{
        ast::{Pattern as KorePattern, Sort as KoreSort, Variable, VariableKind},
        codec,
    },
};
use num_bigint::BigInt;

use crate::{
    assemble::build_backend,
    engine::{
        ConfigurationBuilder,
        proposer::{Observation, Origin, Proposal, ProposalContext, Proposer},
    },
    report::{
        SOLVE_BUDGET_SHARE, SOLVE_FUTILE_LIMIT, SOLVE_MAX_MODEL_QUERIES,
        SOLVE_MODEL_RESOURCE_UNITS, SOLVE_MODEL_RETRIES, SOLVE_PENDING_LIMIT,
        SOLVE_RUN_RESOURCE_UNITS, SOLVE_RUN_RETRIES, SOLVE_STALL_CASES, SOLVE_WORK_FACTOR,
        SOLVE_WORK_SLACK, SolveTotals, Totals,
    },
    score::Score,
    spec::{CaseOptions, ProposerKind},
    values::{self, Constraints, GenerationBounds, Value, ValueSort},
};

/// The stack of a query's thread when the caller gives no thread stack size: the executable's
/// campaign thread size (README, "Command line"). It is reserved, not committed.
const DEFAULT_STACK_SIZE: u64 = 256 << 20;

/// The sort of the configurations a query conjoins constraints to.
const TOP_SORT: &str = "SortGeneratedTopCell";

/// The KORE symbol of `_<=Int_`, which states a range bound.
const INT_LE: &str = "Lbl'Unds-LT-Eqls'Int'Unds'";

/// A hole sort the proposer makes symbolic.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub(crate) enum Symbolic {
    Int,
    Bool,
}

impl Symbolic {
    /// The symbolic sort of a hole of `sort`: `Int` and `Bool` themselves. A sort hooked to them
    /// under another name (`ValueSort::Renamed`) has its domain values at its own KORE sort,
    /// where a `SortInt` variable would be ill-sorted, so it is not made symbolic.
    fn of(sort: &ValueSort) -> Option<Self> {
        match sort {
            ValueSort::Int => Some(Self::Int),
            ValueSort::Bool => Some(Self::Bool),
            _ => None,
        }
    }

    fn kore_sort(self) -> KoreSort {
        KoreSort::Application {
            name: match self {
                Self::Int => "SortInt",
                Self::Bool => "SortBool",
            }
            .into(),
            arguments: Vec::new(),
        }
    }

    /// Whether `value` is a value of this sort.
    fn holds(self, value: &Value) -> bool {
        matches!(
            (self, value),
            (Self::Int, Value::Int(_)) | (Self::Bool, Value::Bool(_))
        )
    }
}

/// What the proposer needs of one hole.
#[derive(Clone, Debug)]
pub(crate) struct SolveHole {
    /// The hole's sort.
    pub(crate) sort: ValueSort,
    /// The hole's declared constraints.
    pub(crate) constraints: Constraints,
}

impl SolveHole {
    /// The symbolic sort of the hole, when it can be made symbolic: an `Int` or `Bool` hole
    /// with more than one admissible value.
    fn symbolic(&self) -> Option<Symbolic> {
        let fixed = self
            .constraints
            .choices
            .as_ref()
            .is_some_and(|choices| choices.len() <= 1);
        Symbolic::of(&self.sort).filter(|_| !fixed)
    }
}

/// The holes a query makes symbolic, in hole order: those that can be made symbolic
/// ([`SolveHole::symbolic`]) and whose value in `values` is among `read`, the values the
/// blocking condition's atoms read (module documentation, "Which holes are symbolic").
pub(crate) fn symbolic_holes(holes: &[SolveHole], values: &[Value], read: &[Value]) -> Vec<usize> {
    holes
        .iter()
        .zip(values)
        .enumerate()
        .filter(|(_, (hole, value))| {
            hole.symbolic()
                .is_some_and(|sort| sort.holds(value) && read.contains(value))
        })
        .map(|(index, _)| index)
        .collect()
}

/// The variable that stands for hole `hole` in a query.
fn variable(hole: usize, sort: Symbolic) -> Variable {
    Variable {
        kind: VariableKind::Element,
        name: format!("VarKrustFuzzHole{hole}"),
        sort: sort.kore_sort(),
    }
}

/// The hole a query variable named `name` stands for.
fn hole_of(name: &str) -> Option<usize> {
    name.strip_prefix("VarKrustFuzzHole")?.parse().ok()
}

/// The values a model `substitution` (a conjunction of `\equals(variable, value)`, as
/// `Backend::get_model` answers) gives the query's variables, by hole: `Int` and `Bool` domain
/// values only, under injections; anything else is left out.
pub(crate) fn model_values(substitution: &KorePattern) -> BTreeMap<usize, Value> {
    let mut found = BTreeMap::new();
    let mut work = vec![substitution];
    while let Some(pattern) = work.pop() {
        match pattern {
            KorePattern::And { arguments, .. } => work.extend(arguments),
            KorePattern::Equals { left, right, .. } => {
                let ((KorePattern::Variable(variable), value)
                | (value, KorePattern::Variable(variable))) = (left.as_ref(), right.as_ref())
                else {
                    continue;
                };
                if let (Some(hole), Some(value)) = (hole_of(&variable.name), domain_value(value)) {
                    found.insert(hole, value);
                }
            }
            _ => {}
        }
    }
    found
}

/// An `Int` or `Bool` domain value, under injections.
fn domain_value(pattern: &KorePattern) -> Option<Value> {
    match pattern {
        KorePattern::DomainValue { sort, value } => {
            let KoreSort::Application { name, .. } = sort else {
                return None;
            };
            let text = value.as_utf8().ok()?;
            match name.as_str() {
                "SortInt" => text.parse::<BigInt>().ok().map(Value::Int),
                "SortBool" => match text {
                    "true" => Some(Value::Bool(true)),
                    "false" => Some(Value::Bool(false)),
                    _ => None,
                },
                _ => None,
            }
        }
        KorePattern::Application { symbol, arguments }
            if symbol.name == "inj" && arguments.len() == 1 =>
        {
            domain_value(&arguments[0])
        }
        _ => None,
    }
}

/// The candidate `model` gives `query`: its values with each symbolic hole the model binds set
/// to the model's value (a symbolic hole it leaves free keeps its value); `None` when the model
/// binds no symbolic hole, which would only give the blocked case back.
fn apply_model(query: &Query, model: &BTreeMap<usize, Value>) -> Option<Vec<Value>> {
    let mut values = query.values.clone();
    let mut bound = false;
    for &hole in &query.symbolic {
        if let Some(value) = model.get(&hole) {
            values[hole] = value.clone();
            bound = true;
        }
    }
    bound.then_some(values)
}

/// The KORE text of `value`, of a symbolic sort.
fn literal(value: &Value) -> Option<String> {
    match value {
        Value::Int(number) => Some(format!(r#"\dv{{SortInt{{}}}}("{number}")"#)),
        Value::Bool(flag) => Some(format!(r#"\dv{{SortBool{{}}}}("{flag}")"#)),
        _ => None,
    }
}

/// The declared constraints of hole `hole` over its query variable, as KORE predicates of the
/// configuration's sort: each range bound as `\equals(true, _<=Int_(..))`, a choice set as the
/// disjunction of equalities; `None` when a constraint has no such form.
fn constraint_predicates(
    hole: usize,
    sort: Symbolic,
    constraints: &Constraints,
) -> Option<Vec<String>> {
    let variable = format!(
        "VarKrustFuzzHole{hole}:{}{{}}",
        match sort {
            Symbolic::Int => "SortInt",
            Symbolic::Bool => "SortBool",
        }
    );
    let mut predicates = Vec::new();
    if let Some(range) = &constraints.range {
        let bound = |left: &str, right: &str| {
            format!(
                r#"\equals{{SortBool{{}}, {TOP_SORT}{{}}}}(\dv{{SortBool{{}}}}("true"), {INT_LE}{{}}({left}, {right}))"#
            )
        };
        if let Some(min) = &range.min {
            predicates.push(bound(&literal(&Value::Int(min.clone()))?, &variable));
        }
        if let Some(max) = &range.max {
            predicates.push(bound(&variable, &literal(&Value::Int(max.clone()))?));
        }
    }
    if let Some(choices) = &constraints.choices {
        let sort_text = match sort {
            Symbolic::Int => "SortInt{}",
            Symbolic::Bool => "SortBool{}",
        };
        let mut disjunction: Option<String> = None;
        for choice in choices.iter().rev() {
            let equality = format!(
                r"\equals{{{sort_text}, {TOP_SORT}{{}}}}({variable}, {})",
                literal(choice)?
            );
            disjunction = Some(match disjunction {
                None => equality,
                Some(rest) => format!(r"\or{{{TOP_SORT}{{}}}}({equality}, {rest})"),
            });
        }
        predicates.extend(disjunction);
    }
    Some(predicates)
}

/// A query the proposer is ready to ask.
#[derive(Clone, Debug)]
struct Query {
    /// The blocked rule's catalog id.
    rule: String,
    /// The blocked case's values.
    values: Vec<Value>,
    /// The symbolic holes, in hole order.
    symbolic: Vec<usize>,
    /// The blocked case's work, which scales the symbolic run's bound.
    work: u64,
}

impl Query {
    /// What identifies the query: the rule, the symbolic holes and the other holes' values. Two
    /// blocked cases that differ only in the symbolic holes' values ask the same question.
    fn key(&self) -> (String, Vec<usize>, Vec<Value>) {
        let concrete = self
            .values
            .iter()
            .enumerate()
            .filter(|(index, _)| !self.symbolic.contains(index))
            .map(|(_, value)| value.clone())
            .collect();
        (self.rule.clone(), self.symbolic.clone(), concrete)
    }
}

/// The key of a query ([`Query::key`]).
type Key = (String, Vec<usize>, Vec<Value>);

/// An unsettled query and the rank of the blocked case it came from (smaller is nearer the
/// target), with the observation order that breaks ties.
#[derive(Clone, Debug)]
struct Pending {
    rank: (u64, crate::score::Guard),
    order: u64,
    query: Query,
}

/// How a symbolic run ended.
#[derive(Debug)]
enum Answer {
    /// A satisfiable leaf: the values its model gives the query's variables, by hole.
    Model(BTreeMap<usize, Value>),
    NoPath,
    Unsatisfiable,
    Unknown,
    Failed(String),
}

/// A symbolic run's answer, its work and whether it lies outside the determinism contract.
#[derive(Debug)]
struct Outcome {
    answer: Answer,
    work: u64,
    outside_determinism: bool,
}

/// Where a query's backend comes from: a copy of the campaign's internalized definition, or, on
/// the `from-definition` route, the compiled definition it internalizes.
enum BackendSource<'a> {
    Internalized(&'a BackendDefinition),
    Compiled(&'a crate::spec::CompiledDefinition),
}

/// Everything one symbolic run reads.
struct RunInput<'a> {
    source: BackendSource<'a>,
    options: BackendOptions,
    /// The options of the backend that answers the model queries.
    model_options: BackendOptions,
    request: ExecuteRequest,
}

impl BackendSource<'_> {
    /// A fresh backend over the source, with `options`.
    fn backend(&self, options: BackendOptions) -> Result<Backend, String> {
        match self {
            BackendSource::Internalized(definition) => {
                Backend::from_internalized(BackendDefinition::clone(definition), options)
                    .map_err(|error| error.to_string())
            }
            BackendSource::Compiled(definition) => {
                build_backend(definition, options).map_err(|error| error.to_string())
            }
        }
    }
}

/// The unique ids of the rewrite steps on `leaf`'s path whose results exist: every `rewrite`
/// trace entry, but for a `work-bound`, `timeout` or `cancelled` leaf the last one, whose state
/// was taken from the worklist unnormalized and may still be `\bottom`.
fn established(leaf: &ExecutionLeaf) -> impl Iterator<Item = &str> {
    let stopped = matches!(
        leaf.reason,
        HaltReasonOutput::WorkBound | HaltReasonOutput::Timeout | HaltReasonOutput::Cancelled
    );
    let rewrites: Vec<&str> = leaf
        .trace
        .iter()
        .filter(|entry| entry.kind == "rewrite")
        .map(|entry| entry.unique_id.as_str())
        .collect();
    let keep = rewrites.len() - usize::from(stopped && !rewrites.is_empty());
    rewrites.into_iter().take(keep)
}

/// Run `input` and query the leaves whose paths applied the blocked rule `rule_id` (module
/// documentation, "The query"), on the calling thread, within the current cancellation scope.
fn run_query(input: RunInput<'_>, rule_id: &str) -> Outcome {
    let failed = |message: String, outside_determinism: bool| Outcome {
        answer: Answer::Failed(message),
        work: 0,
        outside_determinism,
    };
    let mut backend = match input.source.backend(input.options) {
        Ok(backend) => backend,
        Err(message) => return failed(message, false),
    };
    let result = match backend.execute(input.request) {
        Ok(result) => result,
        Err(error) => return failed(error.to_string(), error.stop_cause().is_some()),
    };
    // Unknown answers of the clock-free solver are a function of the query, so they do not count.
    let outside_determinism = result.stack_stops > 0
        || result.leaves.iter().any(|leaf| {
            matches!(
                leaf.reason,
                HaltReasonOutput::Timeout | HaltReasonOutput::Cancelled
            )
        });
    let mut work = result.work;
    let arrived: Vec<_> = result
        .leaves
        .iter()
        .filter(|leaf| established(leaf).any(|rule| rule == rule_id))
        .take(usize::try_from(SOLVE_MAX_MODEL_QUERIES).unwrap_or(usize::MAX))
        .collect();
    if arrived.is_empty() {
        return Outcome {
            answer: Answer::NoPath,
            work,
            outside_determinism,
        };
    }
    // A model query is the solver's real work, so it gets a backend of its own with a larger
    // unit budget than the run's decisions ([`SOLVE_MODEL_RESOURCE_UNITS`]).
    let mut backend = match input.source.backend(input.model_options) {
        Ok(backend) => backend,
        Err(message) => return failed(message, false),
    };
    let mut unknown = false;
    let mut undecodable = false;
    for leaf in arrived {
        work += 1;
        let Ok(state) = codec::from_value(&leaf.state) else {
            undecodable = true;
            continue;
        };
        let model = match backend.get_model(PatternRequest::new(state)) {
            Ok(model) => model,
            Err(error) => {
                return Outcome {
                    answer: Answer::Failed(error.to_string()),
                    work,
                    outside_determinism: outside_determinism || error.stop_cause().is_some(),
                };
            }
        };
        match model.satisfiable.as_str() {
            "sat" => {
                let values = model
                    .substitution
                    .as_ref()
                    .and_then(|substitution| codec::from_value(substitution).ok())
                    .map(|substitution| model_values(&substitution))
                    .unwrap_or_default();
                return Outcome {
                    answer: Answer::Model(values),
                    work,
                    outside_determinism,
                };
            }
            "unsat" => {}
            _ => unknown = true,
        }
    }
    Outcome {
        answer: if unknown {
            Answer::Unknown
        } else if undecodable {
            Answer::Failed("a leaf's state does not decode as KORE".into())
        } else {
            Answer::Unsatisfiable
        },
        work,
        outside_determinism,
    }
}

/// [`run_query`] on a thread of its own with a stack of `stack_size` bytes, so that its solver
/// work shares no Z3 context with the campaign's thread (module documentation,
/// "Determinism"). A cancellation of `cancel`, or the passing of `limit`, stops it.
fn run_isolated(
    input: RunInput<'_>,
    rule: String,
    stack_size: usize,
    cancel: Option<&CancellationToken>,
    limit: Option<Duration>,
) -> Outcome {
    let token = CancellationToken::new();
    let deadline = limit.map(|limit| Instant::now() + limit);
    let caller = thread::current();
    thread::scope(|scope| {
        let worker = {
            let token = token.clone();
            let caller = caller.clone();
            thread::Builder::new()
                .name("krust-fuzz-solve".into())
                .stack_size(stack_size)
                .spawn_scoped(scope, move || {
                    let outcome = token.scope(|| run_query(input, &rule));
                    caller.unpark();
                    outcome
                })
        };
        let worker = match worker {
            Ok(worker) => worker,
            Err(error) => {
                return Outcome {
                    answer: Answer::Failed(format!("the query's thread did not start: {error}")),
                    work: 0,
                    outside_determinism: false,
                };
            }
        };
        if cancel.is_some() || deadline.is_some() {
            while !worker.is_finished() {
                if cancel.is_some_and(CancellationToken::is_cancelled)
                    || deadline.is_some_and(|deadline| Instant::now() >= deadline)
                {
                    token.cancel();
                }
                thread::park_timeout(Duration::from_millis(5));
            }
        }
        let mut outcome = worker.join().unwrap_or_else(|_| Outcome {
            answer: Answer::Failed("the query panicked".into()),
            work: 0,
            outside_determinism: false,
        });
        if token.is_cancelled() {
            outcome.outside_determinism = true;
        }
        outcome
    })
}

/// The solve proposer (module documentation).
pub(crate) struct SolveProposer {
    builder: ConfigurationBuilder,
    holes: Vec<SolveHole>,
    options: CaseOptions,
    bounds: GenerationBounds,
    stack_size: usize,
    cancel: Option<CancellationToken>,
    /// The best score of any case so far, and the cases observed since it last improved.
    best: Option<Score>,
    stalled: u64,
    /// The unsettled queries, one per key, each from the best-ranked blocked case that asks it,
    /// at most [`SOLVE_PENDING_LIMIT`] (module documentation, "When it runs").
    pending: BTreeMap<Key, Pending>,
    /// The keys of the queries whose answer was decided.
    settled: BTreeSet<Key>,
    /// Per blocked rule and set of symbolic holes, the settled queries that gave no candidate;
    /// at [`SOLVE_FUTILE_LIMIT`] the pair is given up for the campaign.
    futile: BTreeMap<(String, Vec<usize>), u64>,
    /// The observed cases, which orders the pending queries of equal rank.
    observed: u64,
    ready: Option<Query>,
    /// The unit budgets of a run's decisions and of a model query ([`SOLVE_RUN_RESOURCE_UNITS`],
    /// [`SOLVE_MODEL_RESOURCE_UNITS`]); fields so that the measurements can vary them.
    run_units: u32,
    model_units: u32,
    run_retries: u32,
    model_retries: u32,
    extra_work: u64,
    totals: SolveTotals,
}

impl SolveProposer {
    /// A solve proposer over `builder`'s holes and configurations, with the campaign's case
    /// `options` and generation `bounds`; `stack_size` is the caller's thread stack size, when it
    /// gave one, and `cancel` the campaign's cancellation.
    pub(crate) fn new(
        builder: ConfigurationBuilder,
        options: CaseOptions,
        bounds: GenerationBounds,
        stack_size: Option<u64>,
        cancel: Option<CancellationToken>,
    ) -> Self {
        let holes = builder
            .holes()
            .holes
            .iter()
            .map(|hole| SolveHole {
                sort: hole.sort.clone(),
                constraints: hole.decl.constraints.clone(),
            })
            .collect();
        Self {
            builder,
            holes,
            options,
            bounds,
            stack_size: usize::try_from(stack_size.unwrap_or(DEFAULT_STACK_SIZE))
                .unwrap_or(usize::MAX),
            cancel,
            best: None,
            stalled: 0,
            pending: BTreeMap::new(),
            settled: BTreeSet::new(),
            futile: BTreeMap::new(),
            observed: 0,
            ready: None,
            run_units: SOLVE_RUN_RESOURCE_UNITS,
            model_units: SOLVE_MODEL_RESOURCE_UNITS,
            run_retries: SOLVE_RUN_RETRIES,
            model_retries: SOLVE_MODEL_RETRIES,
            extra_work: 0,
            totals: SolveTotals::default(),
        }
    }

    /// The query to ask when the search stalls: the pending query of least rank, the first
    /// observed of equal ones.
    fn next_query(&self) -> Option<Query> {
        if self.stalled < SOLVE_STALL_CASES {
            return None;
        }
        self.pending
            .values()
            .min_by(|a, b| (&a.rank, a.order).cmp(&(&b.rank, b.order)))
            .map(|pending| pending.query.clone())
    }

    /// Whether `query`'s blocked rule and symbolic holes were given up ([`SOLVE_FUTILE_LIMIT`]).
    fn given_up(&self, query: &Query) -> bool {
        self.futile
            .get(&(query.rule.clone(), query.symbolic.clone()))
            .is_some_and(|count| *count >= SOLVE_FUTILE_LIMIT)
    }

    /// Keep the query a blocked case asks, unless it is settled or given up; a key already pending keeps the
    /// better-ranked case. Beyond [`SOLVE_PENDING_LIMIT`] keys the worst-ranked (the last
    /// observed of equal ones) is dropped.
    fn keep(&mut self, blocked: &crate::score::Blocked, values: &[Value], work: u64) {
        let symbolic = symbolic_holes(&self.holes, values, &blocked.values);
        if symbolic.is_empty() {
            return;
        }
        let query = Query {
            rule: blocked.rule.clone(),
            values: values.to_vec(),
            symbolic,
            work,
        };
        let key = query.key();
        if self.settled.contains(&key) || self.given_up(&query) {
            return;
        }
        let rank = (blocked.distance, blocked.guard.clone());
        let order = self.observed;
        match self.pending.get_mut(&key) {
            Some(pending) if rank < pending.rank => {
                *pending = Pending { rank, order, query };
            }
            Some(_) => {}
            None => {
                self.pending.insert(key, Pending { rank, order, query });
            }
        }
        if u64::try_from(self.pending.len()).unwrap_or(u64::MAX) > SOLVE_PENDING_LIMIT
            && let Some(worst) = self
                .pending
                .iter()
                .max_by(|(_, a), (_, b)| (&a.rank, a.order).cmp(&(&b.rank, b.order)))
                .map(|(key, _)| key.clone())
        {
            self.pending.remove(&worst);
        }
    }

    /// The initial state of `query`: the blocked case's configuration with the symbolic holes'
    /// variables, and their declared constraints conjoined.
    fn state(&self, query: &Query) -> Result<KorePattern, String> {
        let mut replacements = vec![None; self.holes.len()];
        let mut predicates = Vec::new();
        for &hole in &query.symbolic {
            let sort = self.holes[hole]
                .symbolic()
                .expect("a symbolic hole has a symbolic sort");
            replacements[hole] = Some(KorePattern::Variable(variable(hole, sort)));
            predicates.extend(
                constraint_predicates(hole, sort, &self.holes[hole].constraints)
                    .ok_or("a constraint has no KORE form")?,
            );
        }
        let mut state = self
            .builder
            .configuration(&query.values, &replacements)
            .map_err(|reason| format!("the symbolic configuration was refused: {reason:?}"))?;
        let top = KoreSort::Application {
            name: TOP_SORT.into(),
            arguments: Vec::new(),
        };
        for predicate in predicates {
            let predicate = k_rust::kore::parser::parse_pattern(&predicate)
                .map_err(|error| format!("a constraint does not parse: {error}"))?;
            state = KorePattern::And {
                sort: top.clone(),
                arguments: vec![state, predicate],
            };
        }
        Ok(state)
    }

    /// Count a failed run, keeping the first failure's message.
    fn fail(&mut self, message: String) {
        self.totals.failed += 1;
        self.totals.first_failure.get_or_insert(message);
    }

    /// Ask `query`; the candidate values when its model gives admissible ones. Every answer
    /// settles the query: the clock-free solver answers the same query the same way again, and a
    /// run a cancellation or the per-case safety limit stopped would be stopped again (asking it
    /// at every draw would spend the campaign's time on it while charging little work).
    fn ask(&mut self, query: &Query) -> Option<Vec<Value>> {
        self.totals.attempts += 1;
        let state = match self.state(query) {
            Ok(state) => state,
            Err(message) => {
                self.fail(message);
                return None;
            }
        };
        let request = ExecuteRequest {
            max_depth: self.options.max_depth,
            max_work: Some(
                SOLVE_WORK_FACTOR
                    .saturating_mul(query.work)
                    .saturating_add(SOLVE_WORK_SLACK),
            ),
            max_simplification_iterations: self.options.max_simplification_iterations,
            strategy: ExecutionStrategy::All,
            result_modality: ResultModalityOutput::PathSet,
            trace: true,
            cancelled_result: CancelledResultOutput::Error,
            ..ExecuteRequest::new(state)
        };
        let source = match self.builder.internalized() {
            Some(definition) => BackendSource::Internalized(definition),
            None => BackendSource::Compiled(self.builder.definition()),
        };
        let clock_free = |units: u32, retries: u32| BackendOptions {
            smt_retry_limit: retries,
            smt_resource_limit: NonZeroU32::new(units),
            ..self.options.backend.options()
        };
        let input = RunInput {
            source,
            options: clock_free(self.run_units, self.run_retries),
            model_options: clock_free(self.model_units, self.model_retries),
            request,
        };
        let outcome = run_isolated(
            input,
            query.rule.clone(),
            self.stack_size,
            self.cancel.as_ref(),
            self.options.safety_limit_ms.map(Duration::from_millis),
        );
        // Every run is charged at least 1, a stopped one too (it reports no work), so that its
        // share fills as any case's does.
        let work = outcome.work.max(1);
        self.extra_work = self.extra_work.saturating_add(work);
        self.totals.work = self.totals.work.saturating_add(work);
        if outcome.outside_determinism {
            self.totals.outside_determinism += 1;
        }
        match outcome.answer {
            Answer::Model(model) => match apply_model(query, &model) {
                None => {
                    // A model that gives no symbolic hole a value would propose the blocked case
                    // again.
                    self.fail("the model gives no symbolic hole a value".into());
                    None
                }
                Some(values) => {
                    let admissible = query.symbolic.iter().all(|&hole| {
                        values::admissible(
                            &values[hole],
                            &self.holes[hole].sort,
                            &self.holes[hole].constraints,
                            &self.bounds,
                        )
                    });
                    if admissible {
                        self.totals.candidates += 1;
                        Some(values)
                    } else {
                        self.totals.inadmissible += 1;
                        None
                    }
                }
            },
            Answer::NoPath => {
                self.totals.no_path += 1;
                None
            }
            Answer::Unsatisfiable => {
                self.totals.unsatisfiable += 1;
                None
            }
            Answer::Unknown => {
                self.totals.unknown += 1;
                None
            }
            Answer::Failed(message) => {
                self.fail(message);
                None
            }
        }
    }
}

impl Proposer for SolveProposer {
    fn kind(&self) -> ProposerKind {
        ProposerKind::Solve
    }

    fn ready(&self) -> bool {
        self.ready.is_some()
    }

    fn budget_share(&self) -> Option<(u32, u32)> {
        Some(SOLVE_BUDGET_SHARE)
    }

    fn may_propose_later(&self) -> bool {
        true
    }

    fn take_extra_work(&mut self) -> u64 {
        std::mem::take(&mut self.extra_work)
    }

    fn contribute(&self, totals: &mut Totals) {
        totals.solve = Some(self.totals.clone());
    }

    fn propose(&mut self, _context: &mut ProposalContext<'_>) -> Option<Proposal> {
        let query = self.ready.take()?;
        let key = query.key();
        let values = self.ask(&query);
        // Every asked query is settled (`Self::ask`).
        self.pending.remove(&key);
        self.settled.insert(key);
        if values.is_none() {
            let pair = (query.rule.clone(), query.symbolic.clone());
            let count = self.futile.entry(pair.clone()).or_insert(0);
            *count += 1;
            if *count >= SOLVE_FUTILE_LIMIT {
                self.pending
                    .retain(|(rule, symbolic, _), _| (rule, symbolic) != (&pair.0, &pair.1));
            }
        }
        let values = values?;
        Some(Proposal::plain(
            Origin::Scheduled(ProposerKind::Solve),
            values,
        ))
    }

    fn observe(&mut self, _proposal: &Proposal, _observation: &Observation, _interesting: bool) {}

    fn observe_all(&mut self, proposal: &Proposal, observation: &Observation) {
        match &observation.score {
            Some(score) if self.best.as_ref().is_none_or(|best| score < best) => {
                self.best = Some(score.clone());
                self.stalled = 0;
            }
            _ => self.stalled = self.stalled.saturating_add(1),
        }
        if let Some(blocked) = &observation.blocked {
            self.keep(blocked, &proposal.values, observation.work);
        }
        self.observed += 1;
        self.ready = self.next_query();
    }
}

#[cfg(test)]
#[path = "solve_tests.rs"]
mod tests;
