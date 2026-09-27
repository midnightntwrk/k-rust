use k_rust::backend::TransitionIdOutput;
use k_rust::kore::ast::{Definition as KoreDefinition, Pattern, Sentence as KoreSentence, Sort};
use kink_patch::SentenceRef;
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

/// Stable classifications for plan and finite-input failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatternFailureKind {
    MalformedPlan,
    UnknownConstructor,
    InvalidVariable,
    InvalidArm,
    InvalidPayload,
    InvalidSideTable,
    /// A trace constructor differs from the plan vocabulary's constructor of that name.
    VocabularyMismatch,
    /// A trace belongs to another test than the evaluation context.
    TestMismatch,
    BoundsMismatch,
    TerminalMismatch,
    InvalidOrigin,
    /// A relation connects terms whose sorts differ or cannot be decided.
    InvalidTerm,
    InvalidPath,
    InvalidCollection,
    InputError,
}

/// A closed classification plus diagnostic-only detail.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternFailure {
    kind: PatternFailureKind,
    detail: String,
}

impl PatternFailure {
    fn new(kind: PatternFailureKind, detail: impl Into<String>) -> Self {
        Self {
            kind,
            detail: detail.into(),
        }
    }

    #[must_use]
    pub const fn kind(&self) -> PatternFailureKind {
        self.kind
    }
}

impl fmt::Display for PatternFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(formatter, "{:?}: {}", self.kind, self.detail)
    }
}

impl std::error::Error for PatternFailure {}

/// One constructor in an event vocabulary. Payload sorts are KORE sorts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constructor {
    pub name: String,
    pub payload_sorts: Vec<Sort>,
}

/// An event vocabulary: constructor names mapped to their payload sorts.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EventVocabulary {
    constructors: BTreeMap<String, Constructor>,
}

impl EventVocabulary {
    pub fn new(constructors: Vec<Constructor>) -> Result<Self, PatternFailure> {
        let mut map = BTreeMap::new();
        for constructor in constructors {
            if constructor.name.is_empty() {
                return Err(PatternFailure::new(
                    PatternFailureKind::UnknownConstructor,
                    "constructor names must be nonempty",
                ));
            }
            if let Some(previous) = map.insert(constructor.name.clone(), constructor) {
                return Err(PatternFailure::new(
                    PatternFailureKind::UnknownConstructor,
                    format!("constructor {} is declared twice", previous.name),
                ));
            }
        }
        Ok(Self { constructors: map })
    }

    #[must_use]
    pub fn constructor(&self, name: &str) -> Option<&Constructor> {
        self.constructors.get(name)
    }
}

/// Result sorts of the KORE symbols that payload and relation terms may use.
///
/// `sort_of` takes a pattern's syntactic sort when it has one, reads `inj{From, To}` as `To`,
/// and otherwise looks up the result sort of a non-parametric symbol.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SymbolSorts {
    symbols: BTreeMap<String, (Vec<Sort>, Sort)>,
}

impl SymbolSorts {
    /// Builds the table from `(symbol, argument sorts, result sort)` rows.
    pub fn new(symbols: impl IntoIterator<Item = (String, Vec<Sort>, Sort)>) -> Self {
        Self {
            symbols: symbols
                .into_iter()
                .map(|(name, arguments, result)| (name, (arguments, result)))
                .collect(),
        }
    }

    /// Every non-parametric symbol declaration of a parsed KORE definition.
    #[must_use]
    pub fn from_definition(definition: &KoreDefinition) -> Self {
        Self::new(
            definition
                .modules
                .iter()
                .flat_map(|module| &module.sentences)
                .filter_map(|sentence| match sentence {
                    KoreSentence::SymbolDeclaration {
                        symbol,
                        argument_sorts,
                        result_sort,
                        ..
                    } if symbol.sort_parameters.is_empty() => Some((
                        symbol.name.clone(),
                        argument_sorts.clone(),
                        result_sort.clone(),
                    )),
                    _ => None,
                }),
        )
    }

    /// The sort of `pattern`, or `None` when this table cannot decide it.
    #[must_use]
    pub fn sort_of(&self, pattern: &Pattern) -> Option<Sort> {
        if let Some(sort) = pattern.syntactic_sort() {
            return Some(sort.clone());
        }
        match pattern {
            Pattern::Application { symbol, .. }
            | Pattern::AssociativeApplication { symbol, .. } => {
                match symbol.sort_parameters.as_slice() {
                    [_, to] if symbol.name == "inj" => Some(to.clone()),
                    [] => self
                        .symbols
                        .get(&symbol.name)
                        .map(|(_, result)| result.clone()),
                    _ => None,
                }
            }
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Binding {
    pub name: String,
    pub term: Pattern,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum MatchMode {
    Bind,
    Use,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PayloadClause {
    pub position: usize,
    pub mode: MatchMode,
    pub variable: String,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Atom {
    pub constructor: String,
    pub payload: Vec<PayloadClause>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Relation {
    NextEvent,
    EventuallyAfter,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternArm {
    pub atoms: Vec<Atom>,
    pub relations: Vec<Relation>,
}

/// A named side condition over a declaration-ordered subset of the plan variables.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SideCondition {
    pub name: String,
    pub input_variables: Vec<String>,
}

/// A validated closed flat nonrecursive DNF plan, bound to the vocabulary it was built against.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternPlan {
    pub variables: Vec<(String, Sort)>,
    pub arms: Vec<PatternArm>,
    pub side_condition: Option<SideCondition>,
    vocabulary: EventVocabulary,
}

impl PatternPlan {
    /// Validates a plan against one vocabulary.
    pub fn new(
        vocabulary: &EventVocabulary,
        variables: Vec<(String, Sort)>,
        arms: Vec<PatternArm>,
        side_condition: Option<SideCondition>,
    ) -> Result<Self, PatternFailure> {
        let mut declared = BTreeMap::new();
        for (name, sort) in &variables {
            if !valid_binding_name(name) || declared.insert(name.clone(), sort).is_some() {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidVariable,
                    format!("invalid or duplicate witness variable {name}"),
                ));
            }
        }
        if arms.is_empty() {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidArm,
                "pattern plan must have at least one arm",
            ));
        }
        for arm in &arms {
            if arm.atoms.is_empty() {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidArm,
                    "pattern arm must have at least one atom",
                ));
            }
            if arm.relations.len() + 1 != arm.atoms.len() {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidArm,
                    "relations must be exactly one fewer than atoms",
                ));
            }
            let mut bound = BTreeSet::new();
            for atom in &arm.atoms {
                let declaration = vocabulary.constructor(&atom.constructor).ok_or_else(|| {
                    PatternFailure::new(
                        PatternFailureKind::UnknownConstructor,
                        format!("unknown constructor {}", atom.constructor),
                    )
                })?;
                let mut previous = None;
                for clause in &atom.payload {
                    if previous.is_some_and(|old| old >= clause.position) {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidPayload,
                            "payload positions must be strictly increasing",
                        ));
                    }
                    previous = Some(clause.position);
                    let variable = &clause.variable;
                    if !valid_binding_name(variable) {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidVariable,
                            format!("invalid payload variable {variable}"),
                        ));
                    }
                    let Some(variable_sort) = declared.get(variable) else {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidVariable,
                            format!("undeclared payload variable {variable}"),
                        ));
                    };
                    let Some(payload_sort) = declaration.payload_sorts.get(clause.position) else {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidPayload,
                            "payload position exceeds constructor arity",
                        ));
                    };
                    if payload_sort != *variable_sort {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidPayload,
                            "payload, variable, and vocabulary sorts disagree",
                        ));
                    }
                    match clause.mode {
                        MatchMode::Bind if !bound.insert(variable.clone()) => {
                            return Err(PatternFailure::new(
                                PatternFailureKind::InvalidVariable,
                                format!("variable {variable} is bound more than once"),
                            ));
                        }
                        MatchMode::Use if !bound.contains(variable) => {
                            return Err(PatternFailure::new(
                                PatternFailureKind::InvalidVariable,
                                format!("variable {variable} is used before binding"),
                            ));
                        }
                        MatchMode::Bind | MatchMode::Use => {}
                    }
                }
            }
            if bound.len() != declared.len() {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidVariable,
                    "every arm must bind the complete declared interface exactly once",
                ));
            }
        }
        if let Some(side) = &side_condition {
            if side.name.is_empty() {
                return Err(PatternFailure::new(
                    PatternFailureKind::MalformedPlan,
                    "side-condition name must be nonempty",
                ));
            }
            let requested: BTreeSet<_> = side.input_variables.iter().collect();
            let canonical = variables
                .iter()
                .map(|(name, _)| name)
                .filter(|name| requested.contains(name))
                .collect::<Vec<_>>();
            if canonical.len() != side.input_variables.len()
                || canonical
                    .iter()
                    .zip(&side.input_variables)
                    .any(|(l, r)| *l != r)
            {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidVariable,
                    "side-condition inputs must be a declaration-order subset",
                ));
            }
        }
        Ok(Self {
            variables,
            arms,
            side_condition,
            vocabulary: vocabulary.clone(),
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SideConditionResult {
    True,
    False,
    Unknown,
}

/// One side-condition fact: the condition, its named inputs in plan order, and the path
/// predicate it was decided under.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SideConditionRow {
    pub condition: String,
    pub inputs: Vec<Binding>,
    pub path_predicate: Pattern,
    pub result: SideConditionResult,
}

type SideConditionKey = (String, Vec<Binding>, Pattern);

/// Exact finite table lookup; a missing row returns unknown.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SideConditionTable {
    rows: BTreeMap<SideConditionKey, SideConditionResult>,
}

impl SideConditionTable {
    pub fn new(rows: Vec<SideConditionRow>) -> Result<Self, PatternFailure> {
        let mut map = BTreeMap::new();
        for row in rows {
            if row.condition.is_empty()
                || map
                    .insert((row.condition, row.inputs, row.path_predicate), row.result)
                    .is_some()
            {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidSideTable,
                    "side-condition rows must name their condition and have unique keys",
                ));
            }
        }
        Ok(Self { rows: map })
    }

    fn lookup(
        &self,
        condition: &str,
        inputs: Vec<Binding>,
        predicate: &Pattern,
    ) -> SideConditionResult {
        self.rows
            .get(&(condition.to_owned(), inputs, predicate.clone()))
            .copied()
            .unwrap_or(SideConditionResult::Unknown)
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Event {
    pub index: usize,
    pub constructor: String,
    pub payload: Vec<Pattern>,
    pub origin: EventOrigin,
    /// Whether the compiled rule can be attributed to this authored rule.
    pub attribution: EventAttribution,
    pub transition_ordinal: u64,
    pub emission_ordinal: u64,
}

/// A compiled rule may have several authors with incompatible observation specs.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum EventAttribution {
    Certain,
    Unknown(AttributionUnknownReason),
}

/// Typed reason why a compiled event cannot identify an authored rule.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum AttributionUnknownReason {
    DifferentObservationSpecs { authors: Vec<SentenceRef> },
}

/// The rule whose transition emitted an event, and the transition itself.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct EventOrigin {
    pub rule: SentenceRef,
    pub transition: TransitionIdOutput,
}

/// Closed execution terminal kinds carried by a trace.
///
/// `Normal`, `Stuck` and `SemanticCrash` classify a configuration to which no rule applies.
/// `UndefinedStep` is not a classification of the term: the backend showed that a rule applies
/// to every instance of the path's last state and that no instance has a defined successor, so
/// the path ends there after its last committed transition.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExecutionTerminalKind {
    Normal,
    Stuck,
    SemanticCrash,
    UndefinedStep,
}

/// A terminal and its configuration: a crash is its own terminal term.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct ExecutionTerminal {
    pub kind: ExecutionTerminalKind,
    pub state: Pattern,
}

/// Exact finite bounds included in the pattern result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionBounds {
    pub depth: Option<u64>,
    pub time_ms: Option<u64>,
    pub branches: Option<u64>,
    pub results: Option<u64>,
}

/// What one evaluation is checked against: the test, its bounds, the vocabulary of the
/// observed trace, the rules whose transitions were observed, and the symbol sorts of
/// the compiled definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationContext {
    pub test_id: String,
    pub bounds: ExecutionBounds,
    pub vocabulary: EventVocabulary,
    pub selected_rules: BTreeSet<SentenceRef>,
    pub symbol_sorts: SymbolSorts,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct TermRelation {
    pub left: Pattern,
    pub right: Pattern,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PathStop {
    Terminal,
    Stuck,
    /// The path's next step is undefined for every instance: some rule applies and its result
    /// is `\bottom`. The path is complete: its events are exactly the events of its committed
    /// transitions, and the undefined step adds none.
    UndefinedStep,
    MatchFound,
    DepthLimit,
    TimeLimit,
    BranchLimit,
    ResultLimit,
    ResourceLimit,
    SolverUnknown,
    BackendLimit,
    Error,
}

impl PathStop {
    #[must_use]
    pub const fn is_complete(self) -> bool {
        matches!(self, Self::Terminal | Self::Stuck | Self::UndefinedStep)
    }

    /// Whether the events of a path with this stop happened: the path is complete, the
    /// query stopped on it, or a known limit cut a prefix whose feasibility the producer
    /// decided. On a `SolverUnknown`, `BackendLimit` or `Error` path that feasibility is
    /// open, so `evaluate` counts a candidate there as indeterminate, never as a witness.
    /// Exhaustive over `PathStop`.
    #[must_use]
    pub const fn has_real_prefix(self) -> bool {
        match self {
            Self::Terminal
            | Self::Stuck
            | Self::UndefinedStep
            | Self::MatchFound
            | Self::DepthLimit
            | Self::TimeLimit
            | Self::BranchLimit
            | Self::ResultLimit
            | Self::ResourceLimit => true,
            Self::SolverUnknown | Self::BackendLimit | Self::Error => false,
        }
    }
}

/// Actual execution termination, kept distinct from the query-level match stop.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExecutionStop {
    Terminal,
    Stuck,
    UndefinedStep,
    QuerySatisfied,
    DepthLimit,
    TimeLimit,
    BranchLimit,
    ResultLimit,
    ResourceLimit,
    SolverUnknown,
    BackendLimit,
    Error,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PathInput {
    pub test_id: String,
    pub path_ordinal: usize,
    pub path_key: Option<String>,
    pub complete: bool,
    pub stop: PathStop,
    pub execution_stop: ExecutionStop,
    pub execution_terminal: Option<ExecutionTerminal>,
    pub events: Vec<Event>,
    pub path_predicate: Pattern,
    pub equivalences: Vec<TermRelation>,
    pub inequalities: Vec<TermRelation>,
}

/// Why finite path collection stopped and whether undiscovered work remains.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CollectionStop {
    SearchExhausted,
    MatchFound,
    DepthLimit,
    TimeLimit,
    BranchLimit,
    ResultLimit,
    ResourceLimit,
    SolverUnknown,
    BackendLimit,
    /// The producer returned normally but has no record that it explored everything: a k-rust
    /// search, or an execution whose converging branches may have been merged. Treated like
    /// any other incomplete stop.
    ExhaustionUnrecorded,
    Error,
}

/// The producer's claim that a clean search visited no path at all. Constructing one is that
/// claim; only a producer that has such evidence may do so.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EmptySearchDecision;

/// Explicit finite collection evidence. Empty clean exhaustion requires a decision.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectionEvidence {
    pub stop: CollectionStop,
    pub pending_work: u64,
    pub empty_search_decision: Option<EmptySearchDecision>,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SearchPolicy {
    Exhaustive,
    /// Collection may stop at the first path that satisfies the query. That path's
    /// `QuerySatisfied`/`MatchFound` stop must come from evaluating this plan over the
    /// path's trace; a producer that stops on anything else (a configuration pattern, a
    /// result bound) must report the corresponding limit stop instead. `evaluate` rejects
    /// witnesses off the match-found path and a determinate match-found path without one.
    ExistentialFirst,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatternOutcome {
    Match,
    NoMatch,
    Unknown,
    Error,
}

/// Exact query-level options for one evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EvaluationOptions {
    /// Without stable keys, paths are told apart only by their complete trace shape (stops,
    /// terminal, events, path predicate and relations), so two paths with equal shapes are
    /// rejected rather than counted twice or coalesced.
    pub stable_path_keys: bool,
    pub search_policy: SearchPolicy,
    pub input_error: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Witness {
    pub path_ordinal: usize,
    pub path_key: Option<String>,
    pub arm_ordinal: usize,
    pub event_indices: Vec<usize>,
    pub events: Vec<Event>,
    pub bindings: Vec<Binding>,
    /// The relations under which this occurrence holds, in the solved form its decider chose,
    /// sorted and deduplicated. Empty when every `Use` comparison was unconditionally equal;
    /// otherwise the decider answered `Feasibility::Sat` for them on this path.
    pub assumptions: Vec<TermRelation>,
    pub path_predicate: Pattern,
    pub stop_reason: PathStop,
    pub execution_stop_reason: ExecutionStop,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evaluation {
    pub outcome: PatternOutcome,
    pub complete_coverage: bool,
    pub witnesses: Vec<Witness>,
    pub primary_witness: Option<usize>,
    /// For `Unknown`, the least severe incomplete stop in `PathStop` order, never
    /// `MatchFound`: an indeterminate candidate is `SolverUnknown`. Unlike
    /// An earlier limit is retained even when a later path has an error.
    pub failure: Option<PathStop>,
    pub search_policy: SearchPolicy,
    pub bounds: ExecutionBounds,
}

/// How two payload terms relate on one path, given the assumptions already made there.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum RelationDecision {
    /// Equal on every instance of the path that satisfies the assumptions.
    Equal,
    /// Unequal on every instance of the path that satisfies the assumptions.
    Unequal,
    /// Equal exactly on the instances that also satisfy these relations. They are added to
    /// the assumptions; an empty list means `Equal`.
    EqualIf(Vec<TermRelation>),
    Indeterminate,
}

/// Whether a path and a set of assumptions have a common instance.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum Feasibility {
    Sat,
    Unsat,
    Unknown,
}

/// Decides payload relations and the feasibility of witness assumptions for `evaluate_with`.
///
/// An answer must be sound for the path it names: `Unequal` and `Unsat` prune a candidate, so
/// they must be proved; anything the decider cannot prove is `Indeterminate` or `Unknown`,
/// which leaves the candidate indeterminate.
pub trait RelationDecider {
    /// How `left` (a bound value) and `right` (an event payload) relate on `path` when every
    /// relation in `assumed` (sorted, deduplicated) holds.
    fn relate(
        &self,
        path: &PathInput,
        assumed: &[TermRelation],
        left: &Pattern,
        right: &Pattern,
    ) -> RelationDecision;

    /// Whether `path` has an instance satisfying every relation in `assumptions` (sorted,
    /// deduplicated). `evaluate_with` asks only for a nonempty list on a path with a real
    /// prefix, whose own feasibility the producer already decided; `feasible(path, [])` must
    /// therefore be `Sat` on such a path.
    fn feasible(&self, path: &PathInput, assumptions: &[TermRelation]) -> Feasibility;
}

/// The decider behind `evaluate`: equal when structurally equal or related by a path
/// equivalence, unequal through an asserted inequality or when both are ground, and otherwise
/// indeterminate. It never makes an assumption.
///
/// The ground rule assumes constructor-normal payloads: two distinct ground terms that
/// contain function symbols (`1 +Int 1` and `2`) may be equal, and this decider would still
/// call them unequal.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct StructuralDecider;

impl RelationDecider for StructuralDecider {
    fn relate(
        &self,
        path: &PathInput,
        _assumed: &[TermRelation],
        left: &Pattern,
        right: &Pattern,
    ) -> RelationDecision {
        term_relation(left, right, path)
    }

    fn feasible(&self, _path: &PathInput, assumptions: &[TermRelation]) -> Feasibility {
        if assumptions.is_empty() {
            Feasibility::Sat
        } else {
            Feasibility::Unknown
        }
    }
}

/// Everything a path carries except its ordinal and key. In unkeyed mode it is the only way
/// to tell paths apart, and it orders their witnesses independently of the schedule.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
struct TraceShape<'a> {
    complete: bool,
    stop: PathStop,
    execution_stop: ExecutionStop,
    execution_terminal: Option<&'a ExecutionTerminal>,
    events: &'a [Event],
    path_predicate: &'a Pattern,
    equivalences: &'a [TermRelation],
    inequalities: &'a [TermRelation],
}

impl<'a> TraceShape<'a> {
    fn of(path: &'a PathInput) -> Self {
        Self {
            complete: path.complete,
            stop: path.stop,
            execution_stop: path.execution_stop,
            execution_terminal: path.execution_terminal.as_ref(),
            events: &path.events,
            path_predicate: &path.path_predicate,
            equivalences: &path.equivalences,
            inequalities: &path.inequalities,
        }
    }
}

/// Witness order across paths: by stable key, or by trace shape in unkeyed mode. One
/// evaluation uses one mode for every path.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum PathOrder<'a> {
    Key(&'a str),
    Shape(TraceShape<'a>),
}

struct PendingWitness<'a> {
    path_order: PathOrder<'a>,
    witness: Witness,
}

/// Evaluates a validated plan over supplied finite path-local traces with the
/// `StructuralDecider`.
///
/// A witness lies only on a path whose stop has a real prefix (`PathStop::has_real_prefix`);
/// an occurrence on any other path is an indeterminate candidate, so it can leave the
/// outcome `Unknown` but never make it `Match`.
pub fn evaluate(
    context: &EvaluationContext,
    plan: &PatternPlan,
    paths: &[PathInput],
    collection: &CollectionEvidence,
    side_table: Option<&SideConditionTable>,
    options: EvaluationOptions,
) -> Result<Evaluation, PatternFailure> {
    evaluate_with(
        context,
        plan,
        paths,
        collection,
        side_table,
        options,
        &StructuralDecider,
    )
}

/// `evaluate` with an explicit relation decider.
///
/// Each `Use` comparison asks `decider.relate` under the assumptions of the earlier
/// comparisons of the same occurrence. `EqualIf` adds to them, `Unequal` is a mismatch and
/// `Indeterminate` an indeterminate candidate. A complete occurrence with assumptions passes
/// the side condition and the real-prefix gate first, and then needs `decider.feasible`:
/// `Sat` makes it a witness, `Unsat` a mismatch and `Unknown` an indeterminate candidate.
pub fn evaluate_with(
    context: &EvaluationContext,
    plan: &PatternPlan,
    paths: &[PathInput],
    collection: &CollectionEvidence,
    side_table: Option<&SideConditionTable>,
    options: EvaluationOptions,
    decider: &dyn RelationDecider,
) -> Result<Evaluation, PatternFailure> {
    let EvaluationOptions {
        stable_path_keys,
        search_policy,
        input_error,
    } = options;
    validate_context(context)?;
    if input_error {
        return Ok(Evaluation {
            outcome: PatternOutcome::Error,
            complete_coverage: false,
            witnesses: Vec::new(),
            primary_witness: None,
            failure: Some(PathStop::Error),
            search_policy,
            bounds: context.bounds.clone(),
        });
    }
    validate_collection(paths, collection, search_policy)?;
    let mut keyed = BTreeSet::new();
    let mut unkeyed = BTreeSet::new();
    let mut path_ordinals = BTreeSet::new();
    for path in paths {
        validate_path(path, context, plan)?;
        if !path_ordinals.insert(path.path_ordinal) {
            return Err(invalid_path("path ordinals must be unique"));
        }
        if stable_path_keys {
            let Some(key) = &path.path_key else {
                return Err(invalid_path("stable path mode requires a path key"));
            };
            if key.is_empty() || !keyed.insert(key.clone()) {
                return Err(invalid_path("stable path keys must be nonempty and unique"));
            }
        } else if path.path_key.is_some() {
            return Err(invalid_path("unkeyed mode cannot expose a path key"));
        } else if !unkeyed.insert(TraceShape::of(path)) {
            return Err(invalid_path(
                "unkeyed mode cannot distinguish paths with identical traces; supply stable path keys",
            ));
        }
    }
    if path_ordinals != (0..paths.len()).collect() {
        return Err(invalid_path("path ordinals must be contiguous from zero"));
    }

    let mut pending = Vec::new();
    let mut indeterminate = false;
    let mut match_stop_indeterminate = false;
    for path in paths {
        let path_order = match &path.path_key {
            Some(key) => PathOrder::Key(key),
            None => PathOrder::Shape(TraceShape::of(path)),
        };
        let mut path_indeterminate = false;
        // An unattributed event may be absent from the authored vocabulary. That
        // changes adjacency even when its constructor is not an atom of this plan.
        if path
            .events
            .iter()
            .any(|event| matches!(event.attribution, EventAttribution::Unknown(_)))
            && plan
                .arms
                .iter()
                .any(|arm| arm.relations.contains(&Relation::NextEvent))
        {
            path_indeterminate = true;
        }
        for (arm_ordinal, arm) in plan.arms.iter().enumerate() {
            let mut context = ExtendContext {
                plan,
                path,
                arm,
                arm_ordinal,
                side_table,
                decider,
                path_order: &path_order,
                pending: &mut pending,
                indeterminate: &mut path_indeterminate,
            };
            extend_occurrence(&mut context, 0, &[], &BTreeMap::new(), &[]);
        }
        indeterminate |= path_indeterminate;
        match_stop_indeterminate |= path_indeterminate && path.stop == PathStop::MatchFound;
    }
    pending.sort_by(|left, right| {
        left.path_order
            .cmp(&right.path_order)
            .then_with(|| left.witness.event_indices.cmp(&right.witness.event_indices))
            .then_with(|| left.witness.bindings.cmp(&right.witness.bindings))
            .then_with(|| left.witness.assumptions.cmp(&right.witness.assumptions))
            .then_with(|| left.witness.arm_ordinal.cmp(&right.witness.arm_ordinal))
    });
    let witnesses = pending
        .into_iter()
        .map(|item| item.witness)
        .collect::<Vec<_>>();
    if search_policy == SearchPolicy::ExistentialFirst {
        // `validate_collection` admits at most one match-found path; an indeterminate
        // candidate on that path itself is missing evidence, not a dishonest stop. An
        // indeterminate candidate elsewhere does not explain why the stop was taken.
        let stopped = paths.iter().any(|path| path.stop == PathStop::MatchFound);
        if witnesses
            .iter()
            .any(|witness| witness.stop_reason != PathStop::MatchFound)
            || (stopped && witnesses.is_empty() && !match_stop_indeterminate)
        {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidCollection,
                "existential-first witnesses must lie exactly on the match-found path",
            ));
        }
    }
    let complete_coverage = collection.stop == CollectionStop::SearchExhausted
        && collection.pending_work == 0
        && paths.iter().all(|path| path.complete)
        && !indeterminate;
    let outcome = if !witnesses.is_empty() {
        PatternOutcome::Match
    } else if indeterminate || !complete_coverage {
        PatternOutcome::Unknown
    } else {
        PatternOutcome::NoMatch
    };
    let failure = if outcome == PatternOutcome::Unknown {
        // A match-found stop reaches `Unknown` only through its own indeterminate
        // candidate, so it is never the cause; that candidate is reported as
        // `SolverUnknown` unless another incomplete stop is less severe.
        paths
            .iter()
            .filter(|path| !path.complete && path.stop != PathStop::MatchFound)
            .map(|path| path.stop)
            .min()
            .or_else(|| collection_failure(collection.stop))
            .or(Some(PathStop::SolverUnknown))
    } else {
        None
    };
    Ok(Evaluation {
        outcome,
        complete_coverage,
        primary_witness: (stable_path_keys && !witnesses.is_empty()).then_some(0),
        witnesses,
        failure,
        search_policy,
        bounds: context.bounds.clone(),
    })
}

fn validate_context(context: &EvaluationContext) -> Result<(), PatternFailure> {
    if context.test_id.is_empty() {
        return Err(PatternFailure::new(
            PatternFailureKind::InputError,
            "test identity must be nonempty",
        ));
    }
    if context.bounds.time_ms == Some(0)
        || context.bounds.branches == Some(0)
        || context.bounds.results == Some(0)
    {
        return Err(PatternFailure::new(
            PatternFailureKind::BoundsMismatch,
            "time, branch, and result bounds must be positive when present",
        ));
    }
    Ok(())
}

fn validate_collection(
    paths: &[PathInput],
    collection: &CollectionEvidence,
    search_policy: SearchPolicy,
) -> Result<(), PatternFailure> {
    let clean_exhaustion = collection.stop == CollectionStop::SearchExhausted;
    if clean_exhaustion && collection.pending_work != 0 {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidCollection,
            "clean search exhaustion requires zero pending work",
        ));
    }
    if collection.stop == CollectionStop::MatchFound
        && search_policy != SearchPolicy::ExistentialFirst
    {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidCollection,
            "match-found collection stop requires existential-first policy",
        ));
    }
    let match_found_paths = paths
        .iter()
        .filter(|path| path.stop == PathStop::MatchFound)
        .count();
    if (collection.stop == CollectionStop::MatchFound) != (match_found_paths == 1)
        || (match_found_paths != 0 && search_policy != SearchPolicy::ExistentialFirst)
    {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidCollection,
            "query-level match stop must correspond to exactly one existential-first path",
        ));
    }
    if paths.is_empty() && clean_exhaustion {
        if collection.empty_search_decision.is_none() {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidCollection,
                "empty clean exhaustion requires an empty-search decision",
            ));
        }
    } else if collection.empty_search_decision.is_some() {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidCollection,
            "empty-search evidence is valid only for zero-visit clean exhaustion",
        ));
    }
    Ok(())
}

fn validate_path(
    path: &PathInput,
    context: &EvaluationContext,
    plan: &PatternPlan,
) -> Result<(), PatternFailure> {
    if path.test_id != context.test_id {
        return Err(PatternFailure::new(
            PatternFailureKind::TestMismatch,
            "trace test differs from the evaluation context",
        ));
    }
    if path.complete != path.execution_terminal.is_some() {
        return Err(PatternFailure::new(
            PatternFailureKind::TerminalMismatch,
            "trace completeness and terminal evidence disagree",
        ));
    }
    let expected_execution_stop = match path.stop {
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
    };
    if path.execution_stop != expected_execution_stop {
        return Err(PatternFailure::new(
            PatternFailureKind::TerminalMismatch,
            "query-level stop and execution termination are conflated or inconsistent",
        ));
    }
    match (
        path.execution_stop,
        path.execution_terminal.as_ref().map(|item| item.kind),
    ) {
        (
            ExecutionStop::Terminal,
            Some(ExecutionTerminalKind::Normal | ExecutionTerminalKind::SemanticCrash),
        )
        | (ExecutionStop::Stuck, Some(ExecutionTerminalKind::Stuck))
        | (ExecutionStop::UndefinedStep, Some(ExecutionTerminalKind::UndefinedStep))
        | (
            ExecutionStop::QuerySatisfied
            | ExecutionStop::DepthLimit
            | ExecutionStop::TimeLimit
            | ExecutionStop::BranchLimit
            | ExecutionStop::ResultLimit
            | ExecutionStop::ResourceLimit
            | ExecutionStop::SolverUnknown
            | ExecutionStop::BackendLimit
            | ExecutionStop::Error,
            None,
        ) => {}
        _ => {
            return Err(PatternFailure::new(
                PatternFailureKind::TerminalMismatch,
                "trace stop and execution terminal are inconsistent",
            ));
        }
    }
    validate_relations(path, &context.symbol_sorts)?;
    validate_events(path, plan, context)
}

fn validate_events(
    path: &PathInput,
    plan: &PatternPlan,
    context: &EvaluationContext,
) -> Result<(), PatternFailure> {
    let mut previous_transition = None;
    let mut expected_emission = 0;
    for (index, event) in path.events.iter().enumerate() {
        if event.index != index {
            return Err(invalid_path(
                "event indices must be zero-based and contiguous",
            ));
        }
        if let Some(constructor) = context.vocabulary.constructor(&event.constructor) {
            if let Some(plan_constructor) = plan.vocabulary.constructor(&event.constructor)
                && plan_constructor != constructor
            {
                return Err(PatternFailure::new(
                    PatternFailureKind::VocabularyMismatch,
                    "trace constructor differs from the plan vocabulary",
                ));
            }
            if matches!(event.attribution, EventAttribution::Certain)
                && (event.payload.len() != constructor.payload_sorts.len()
                    || event
                        .payload
                        .iter()
                        .zip(&constructor.payload_sorts)
                        .any(|(term, sort)| {
                            context.symbol_sorts.sort_of(term).as_ref() != Some(sort)
                        }))
            {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidPayload,
                    "trace event payload arity or sort differs from the vocabulary",
                ));
            }
        } else if matches!(event.attribution, EventAttribution::Certain) {
            return Err(PatternFailure::new(
                PatternFailureKind::UnknownConstructor,
                format!("trace contains unknown constructor {}", event.constructor),
            ));
        }
        if matches!(event.attribution, EventAttribution::Unknown(_)) && !event.payload.is_empty() {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidPayload,
                "unattributed event must not expose a payload",
            ));
        }
        if !context.selected_rules.contains(&event.origin.rule) {
            return Err(invalid_origin(format!(
                "event origin {:?} is not an observed rule",
                event.origin.rule
            )));
        }
        if previous_transition.is_some_and(|previous| event.transition_ordinal < previous) {
            return Err(invalid_path("transition ordinals must be monotonic"));
        }
        if previous_transition != Some(event.transition_ordinal) {
            expected_emission = 0;
        }
        if event.emission_ordinal != expected_emission {
            return Err(invalid_path(
                "emission ordinals must be contiguous within each transition",
            ));
        }
        expected_emission += 1;
        previous_transition = Some(event.transition_ordinal);
    }
    Ok(())
}

struct ExtendContext<'a, 'b> {
    plan: &'a PatternPlan,
    path: &'a PathInput,
    arm: &'a PatternArm,
    arm_ordinal: usize,
    side_table: Option<&'a SideConditionTable>,
    decider: &'a dyn RelationDecider,
    path_order: &'b PathOrder<'a>,
    pending: &'b mut Vec<PendingWitness<'a>>,
    indeterminate: &'b mut bool,
}

fn extend_occurrence(
    context: &mut ExtendContext<'_, '_>,
    atom_ordinal: usize,
    indices: &[usize],
    bindings: &BTreeMap<String, Pattern>,
    assumptions: &[TermRelation],
) {
    if atom_ordinal == context.arm.atoms.len() {
        let ordered = context
            .plan
            .variables
            .iter()
            .map(|(name, _)| Binding {
                name: name.clone(),
                term: bindings
                    .get(name)
                    .expect("validated arm binds every variable")
                    .clone(),
            })
            .collect::<Vec<_>>();
        if let Some(side) = &context.plan.side_condition {
            let inputs = ordered
                .iter()
                .filter(|binding| side.input_variables.contains(&binding.name))
                .cloned()
                .collect::<Vec<_>>();
            let result = context
                .side_table
                .map_or(SideConditionResult::Unknown, |table| {
                    table.lookup(&side.name, inputs, &context.path.path_predicate)
                });
            match result {
                SideConditionResult::False => return,
                SideConditionResult::Unknown => {
                    *context.indeterminate = true;
                    return;
                }
                SideConditionResult::True => {}
            }
        }
        if !context.path.stop.has_real_prefix() {
            // The occurrence may lie on an infeasible path.
            *context.indeterminate = true;
            return;
        }
        if !assumptions.is_empty() {
            match context.decider.feasible(context.path, assumptions) {
                Feasibility::Sat => {}
                Feasibility::Unsat => return,
                Feasibility::Unknown => {
                    *context.indeterminate = true;
                    return;
                }
            }
        }
        context.pending.push(PendingWitness {
            path_order: context.path_order.clone(),
            witness: Witness {
                path_ordinal: context.path.path_ordinal,
                path_key: context.path.path_key.clone(),
                arm_ordinal: context.arm_ordinal,
                event_indices: indices.to_vec(),
                events: indices
                    .iter()
                    .map(|index| context.path.events[*index].clone())
                    .collect(),
                bindings: ordered,
                assumptions: assumptions.to_vec(),
                path_predicate: context.path.path_predicate.clone(),
                stop_reason: context.path.stop,
                execution_stop_reason: context.path.execution_stop,
            },
        });
        return;
    }
    let candidates: Box<dyn Iterator<Item = usize>> = if let Some(previous) = indices.last() {
        match context.arm.relations[atom_ordinal - 1] {
            Relation::NextEvent => Box::new(std::iter::once(previous + 1)),
            Relation::EventuallyAfter => Box::new((previous + 1)..context.path.events.len()),
        }
    } else {
        Box::new(0..context.path.events.len())
    };
    for index in candidates.filter(|index| *index < context.path.events.len()) {
        match match_atom(
            &context.arm.atoms[atom_ordinal],
            &context.path.events[index],
            bindings,
            assumptions,
            context.path,
            context.decider,
        ) {
            AtomMatch::Matched(next, next_assumptions) => {
                let mut next_indices = indices.to_vec();
                next_indices.push(index);
                extend_occurrence(
                    context,
                    atom_ordinal + 1,
                    &next_indices,
                    &next,
                    &next_assumptions,
                );
            }
            AtomMatch::Indeterminate => *context.indeterminate = true,
            AtomMatch::Mismatch => {}
        }
    }
}

enum AtomMatch {
    /// The extended bindings and the extended sorted, deduplicated assumptions.
    Matched(BTreeMap<String, Pattern>, Vec<TermRelation>),
    Indeterminate,
    Mismatch,
}

fn match_atom(
    atom: &Atom,
    event: &Event,
    bindings: &BTreeMap<String, Pattern>,
    assumptions: &[TermRelation],
    path: &PathInput,
    decider: &dyn RelationDecider,
) -> AtomMatch {
    if atom.constructor != event.constructor {
        return AtomMatch::Mismatch;
    }
    if matches!(event.attribution, EventAttribution::Unknown(_)) {
        return AtomMatch::Indeterminate;
    }
    let mut resolved = bindings.clone();
    let mut assumed = assumptions.to_vec();
    for clause in &atom.payload {
        let Some(term) = event.payload.get(clause.position) else {
            return AtomMatch::Mismatch;
        };
        match clause.mode {
            MatchMode::Bind
                if resolved
                    .insert(clause.variable.clone(), term.clone())
                    .is_none() => {}
            MatchMode::Bind => return AtomMatch::Mismatch,
            MatchMode::Use => {
                let Some(bound) = resolved.get(&clause.variable) else {
                    return AtomMatch::Mismatch;
                };
                match decider.relate(path, &assumed, bound, term) {
                    RelationDecision::Equal => {}
                    RelationDecision::EqualIf(relations) => {
                        assumed.extend(relations);
                        assumed.sort();
                        assumed.dedup();
                    }
                    RelationDecision::Unequal => return AtomMatch::Mismatch,
                    RelationDecision::Indeterminate => return AtomMatch::Indeterminate,
                }
            }
        }
    }
    AtomMatch::Matched(resolved, assumed)
}

/// Equal when structurally equal or related by a path equivalence, unequal through an
/// asserted inequality or when both are ground, and otherwise indeterminate.
fn term_relation(left: &Pattern, right: &Pattern, path: &PathInput) -> RelationDecision {
    if left == right || connected(left, right, &path.equivalences) {
        return RelationDecision::Equal;
    }
    if path.inequalities.iter().any(|pair| {
        connected(left, &pair.left, &path.equivalences)
            && connected(right, &pair.right, &path.equivalences)
            || connected(left, &pair.right, &path.equivalences)
                && connected(right, &pair.left, &path.equivalences)
    }) {
        RelationDecision::Unequal
    } else if !left.free_variables().is_empty() || !right.free_variables().is_empty() {
        RelationDecision::Indeterminate
    } else {
        RelationDecision::Unequal
    }
}

fn connected(left: &Pattern, right: &Pattern, relations: &[TermRelation]) -> bool {
    if left == right {
        return true;
    }
    let mut queue = VecDeque::from([left]);
    let mut visited: Vec<&Pattern> = Vec::new();
    while let Some(item) = queue.pop_front() {
        if visited.contains(&item) {
            continue;
        }
        visited.push(item);
        for relation in relations {
            let next = if &relation.left == item {
                Some(&relation.right)
            } else if &relation.right == item {
                Some(&relation.left)
            } else {
                None
            };
            if let Some(next) = next {
                if next == right {
                    return true;
                }
                queue.push_back(next);
            }
        }
    }
    false
}

fn validate_relations(path: &PathInput, sorts: &SymbolSorts) -> Result<(), PatternFailure> {
    for relation in path.equivalences.iter().chain(&path.inequalities) {
        let left = sorts.sort_of(&relation.left);
        if left.is_none() || left != sorts.sort_of(&relation.right) {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidTerm,
                "supplied relation connects terms of different or undecided sorts",
            ));
        }
    }
    if path
        .inequalities
        .iter()
        .any(|pair| connected(&pair.left, &pair.right, &path.equivalences))
    {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidPath,
            "path supplies contradictory equality and inequality",
        ));
    }
    Ok(())
}

fn valid_binding_name(value: &str) -> bool {
    let mut bytes = value.bytes();
    matches!(bytes.next(), Some(b'A'..=b'Z'))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

fn invalid_path(detail: impl Into<String>) -> PatternFailure {
    PatternFailure::new(PatternFailureKind::InvalidPath, detail)
}

fn invalid_origin(detail: impl Into<String>) -> PatternFailure {
    PatternFailure::new(PatternFailureKind::InvalidOrigin, detail)
}

/// The path stop that an incomplete collection stop stands for, as the cause of `Unknown`.
/// Missing exhaustion evidence is a backend limit: the backend cannot say it explored
/// everything.
fn collection_failure(stop: CollectionStop) -> Option<PathStop> {
    match stop {
        CollectionStop::SearchExhausted | CollectionStop::MatchFound => None,
        CollectionStop::DepthLimit => Some(PathStop::DepthLimit),
        CollectionStop::TimeLimit => Some(PathStop::TimeLimit),
        CollectionStop::BranchLimit => Some(PathStop::BranchLimit),
        CollectionStop::ResultLimit => Some(PathStop::ResultLimit),
        CollectionStop::ResourceLimit => Some(PathStop::ResourceLimit),
        CollectionStop::SolverUnknown => Some(PathStop::SolverUnknown),
        CollectionStop::BackendLimit | CollectionStop::ExhaustionUnrecorded => {
            Some(PathStop::BackendLimit)
        }
        CollectionStop::Error => Some(PathStop::Error),
    }
}
