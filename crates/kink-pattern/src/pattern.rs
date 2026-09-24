use kink_portable::{
    Digest, DigestDomain, Provenance, SemanticJson, Term, TermNode, digest, digest_without_field,
};
use std::collections::{BTreeMap, BTreeSet, VecDeque};
use std::fmt;

/// Stable classifications for normalized-plan and finite-input failures.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatternFailureKind {
    MalformedPlan,
    PlanIdentity,
    VocabularyIdentity,
    UnknownConstructor,
    InvalidVariable,
    InvalidArm,
    InvalidPayload,
    QueryIdentity,
    QueryPlanMismatch,
    SideTableIdentity,
    InvalidSideTable,
    DefinitionMismatch,
    BoundsMismatch,
    TerminalMismatch,
    InvalidOrigin,
    InvalidTermGraph,
    InvalidPath,
    InvalidCollection,
    InvalidCorpus,
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

/// A role-typed artifact identity.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ArtifactRef {
    pub role: String,
    pub digest: Digest,
}

/// How event provenance is represented by the vocabulary.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum OriginMode {
    EmittingSentence,
    EmittingSentenceAndSemanticSite,
}

/// One constructor in a canonical event vocabulary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Constructor {
    pub name: String,
    pub payload_sorts: Vec<String>,
    pub origin_mode: OriginMode,
}

/// A digest-checked event vocabulary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EventVocabulary {
    pub digest: Digest,
    constructors: BTreeMap<String, Constructor>,
}

impl EventVocabulary {
    pub fn new(expected: Digest, constructors: Vec<Constructor>) -> Result<Self, PatternFailure> {
        let mut names = BTreeSet::new();
        if constructors
            .iter()
            .any(|item| item.name.is_empty() || item.payload_sorts.iter().any(String::is_empty))
        {
            return Err(PatternFailure::new(
                PatternFailureKind::UnknownConstructor,
                "constructor names and payload sorts must be nonempty",
            ));
        }
        if constructors
            .iter()
            .any(|item| !names.insert(item.name.clone()))
        {
            return Err(PatternFailure::new(
                PatternFailureKind::UnknownConstructor,
                "constructor names must be unique",
            ));
        }
        let mut ordered = constructors;
        ordered.sort_by(|left, right| left.name.cmp(&right.name));
        let value = SemanticJson::Array(ordered.iter().map(Constructor::to_json).collect());
        let actual = checked_domain_digest(
            "k-in-k/event-vocabulary/v1",
            &value,
            PatternFailureKind::VocabularyIdentity,
        )?;
        if actual != expected {
            return Err(PatternFailure::new(
                PatternFailureKind::VocabularyIdentity,
                "event vocabulary digest does not cover the canonical constructor mapping",
            ));
        }
        Ok(Self {
            digest: expected,
            constructors: ordered
                .into_iter()
                .map(|item| (item.name.clone(), item))
                .collect(),
        })
    }

    fn constructor(&self, name: &str) -> Option<&Constructor> {
        self.constructors.get(name)
    }
}

impl Constructor {
    fn to_json(&self) -> SemanticJson {
        object([
            ("constructor", string(&self.name)),
            (
                "payloadSorts",
                SemanticJson::Array(self.payload_sorts.iter().map(|item| string(item)).collect()),
            ),
            (
                "originMode",
                string(match self.origin_mode {
                    OriginMode::EmittingSentence => "emitting-sentence",
                    OriginMode::EmittingSentenceAndSemanticSite => {
                        "emitting-sentence-and-semantic-site"
                    }
                }),
            ),
        ])
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Binding {
    pub name: String,
    pub term: Term,
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

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SideCondition {
    pub artifact: ArtifactRef,
    pub input_variables: Vec<String>,
}

/// A validated closed flat nonrecursive DNF plan.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct PatternPlan {
    pub digest: Digest,
    pub event_vocabulary_digest: Digest,
    pub variables: Vec<(String, String)>,
    pub arms: Vec<PatternArm>,
    pub side_condition: Option<SideCondition>,
    vocabulary: EventVocabulary,
}

impl PatternPlan {
    /// Parses and validates the normalized JSON interchange against one exact vocabulary.
    pub fn from_json(
        value: &SemanticJson,
        vocabulary: &EventVocabulary,
    ) -> Result<Self, PatternFailure> {
        let fields = exact_object(
            value,
            &[
                "schemaVersion",
                "patternPlanDigest",
                "eventVocabularyDigest",
                "variables",
                "arms",
                "sideCondition",
            ],
            "pattern plan",
        )?;
        if integer(fields.get("schemaVersion"), "schemaVersion")? != 1 {
            return Err(malformed("pattern plan schemaVersion must be one"));
        }
        let plan_digest = parsed_digest(fields.get("patternPlanDigest"), "patternPlanDigest")?;
        let expected = digest_without_field(
            &DigestDomain::new("k-in-k/pattern-plan/v1").expect("static domain"),
            value,
            "patternPlanDigest",
        )
        .map_err(|_| malformed("pattern plan self-ID projection failed"))?;
        if plan_digest != expected {
            return Err(PatternFailure::new(
                PatternFailureKind::PlanIdentity,
                "patternPlanDigest does not identify the complete normalized plan",
            ));
        }
        let vocabulary_digest =
            parsed_digest(fields.get("eventVocabularyDigest"), "eventVocabularyDigest")?;
        if vocabulary_digest != vocabulary.digest {
            return Err(PatternFailure::new(
                PatternFailureKind::VocabularyIdentity,
                "plan resolves against a different event vocabulary",
            ));
        }

        let variable_values = array(fields.get("variables"), "variables")?;
        let mut variables = Vec::with_capacity(variable_values.len());
        let mut declared = BTreeMap::new();
        for item in variable_values {
            let item = exact_object(item, &["name", "sort"], "variable")?;
            let name = text(item.get("name"), "variable name")?.to_owned();
            let sort = nonempty(text(item.get("sort"), "variable sort")?, "variable sort")?;
            if !valid_binding_name(&name) || declared.insert(name.clone(), sort.clone()).is_some() {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidVariable,
                    format!("invalid or duplicate witness variable {name}"),
                ));
            }
            variables.push((name, sort));
        }

        let arm_values = array(fields.get("arms"), "arms")?;
        if arm_values.is_empty() {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidArm,
                "pattern plan must have at least one arm",
            ));
        }
        let mut arms = Vec::with_capacity(arm_values.len());
        for arm_value in arm_values {
            let arm_fields = exact_object(arm_value, &["atoms", "relations"], "arm")?;
            let atom_values = array(arm_fields.get("atoms"), "atoms")?;
            if atom_values.is_empty() {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidArm,
                    "pattern arm must have at least one atom",
                ));
            }
            let relation_values = array(arm_fields.get("relations"), "relations")?;
            if relation_values.len() + 1 != atom_values.len() {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidArm,
                    "relations must be exactly one fewer than atoms",
                ));
            }
            let relations = relation_values
                .iter()
                .map(|item| match text(Some(item), "relation")? {
                    "next-event" => Ok(Relation::NextEvent),
                    "eventually-after" => Ok(Relation::EventuallyAfter),
                    other => Err(PatternFailure::new(
                        PatternFailureKind::InvalidArm,
                        format!("unsupported relation {other}"),
                    )),
                })
                .collect::<Result<Vec<_>, _>>()?;
            let mut atoms = Vec::with_capacity(atom_values.len());
            let mut bound = BTreeSet::new();
            for atom_value in atom_values {
                let atom_fields = exact_object(atom_value, &["constructor", "payload"], "atom")?;
                let constructor = nonempty(
                    text(atom_fields.get("constructor"), "constructor")?,
                    "constructor",
                )?;
                let declaration = vocabulary.constructor(&constructor).ok_or_else(|| {
                    PatternFailure::new(
                        PatternFailureKind::UnknownConstructor,
                        format!("unknown constructor {constructor}"),
                    )
                })?;
                let clauses = array(atom_fields.get("payload"), "payload")?;
                let mut payload = Vec::with_capacity(clauses.len());
                let mut previous = None;
                for clause in clauses {
                    let clause =
                        exact_object(clause, &["position", "mode", "variable"], "payload clause")?;
                    let position = usize::try_from(integer(clause.get("position"), "position")?)
                        .map_err(|_| malformed("payload position is negative"))?;
                    if previous.is_some_and(|old| old >= position) {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidPayload,
                            "payload positions must be strictly increasing",
                        ));
                    }
                    previous = Some(position);
                    let variable = text(clause.get("variable"), "payload variable")?.to_owned();
                    if !valid_binding_name(&variable) {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidVariable,
                            format!("invalid payload variable {variable}"),
                        ));
                    }
                    let Some(variable_sort) = declared.get(&variable) else {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidVariable,
                            format!("undeclared payload variable {variable}"),
                        ));
                    };
                    let Some(payload_sort) = declaration.payload_sorts.get(position) else {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidPayload,
                            "payload position exceeds constructor arity",
                        ));
                    };
                    if payload_sort != variable_sort {
                        return Err(PatternFailure::new(
                            PatternFailureKind::InvalidPayload,
                            "payload, variable, and vocabulary sorts disagree",
                        ));
                    }
                    let mode = match text(clause.get("mode"), "payload mode")? {
                        "bind" if bound.insert(variable.clone()) => MatchMode::Bind,
                        "bind" => {
                            return Err(PatternFailure::new(
                                PatternFailureKind::InvalidVariable,
                                format!("variable {variable} is bound more than once"),
                            ));
                        }
                        "use" if bound.contains(&variable) => MatchMode::Use,
                        "use" => {
                            return Err(PatternFailure::new(
                                PatternFailureKind::InvalidVariable,
                                format!("variable {variable} is used before binding"),
                            ));
                        }
                        other => {
                            return Err(PatternFailure::new(
                                PatternFailureKind::InvalidPayload,
                                format!("unsupported payload mode {other}"),
                            ));
                        }
                    };
                    payload.push(PayloadClause {
                        position,
                        mode,
                        variable,
                    });
                }
                atoms.push(Atom {
                    constructor,
                    payload,
                });
            }
            if bound.len() != declared.len() || !declared.keys().all(|name| bound.contains(name)) {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidVariable,
                    "every arm must bind the complete declared interface exactly once",
                ));
            }
            arms.push(PatternArm { atoms, relations });
        }

        let side_condition = match fields.get("sideCondition") {
            Some(SemanticJson::Null) => None,
            Some(value) => {
                let side = exact_object(
                    value,
                    &["artifact", "resultSort", "inputVariables"],
                    "side condition",
                )?;
                if text(side.get("resultSort"), "side-condition result sort")? != "Bool" {
                    return Err(PatternFailure::new(
                        PatternFailureKind::InvalidVariable,
                        "side-condition result sort must be Bool",
                    ));
                }
                let artifact = parse_artifact(side.get("artifact"), "pattern-side-condition")?;
                let requested = array(side.get("inputVariables"), "inputVariables")?
                    .iter()
                    .map(|item| Ok(text(Some(item), "input variable")?.to_owned()))
                    .collect::<Result<Vec<_>, PatternFailure>>()?;
                let requested_set: BTreeSet<_> = requested.iter().cloned().collect();
                let canonical = variables
                    .iter()
                    .filter(|(name, _)| requested_set.contains(name))
                    .map(|(name, _)| name.clone())
                    .collect::<Vec<_>>();
                if requested != canonical || requested_set.len() != requested.len() {
                    return Err(PatternFailure::new(
                        PatternFailureKind::InvalidVariable,
                        "side-condition inputs must be a declaration-order subset",
                    ));
                }
                Some(SideCondition {
                    artifact,
                    input_variables: requested,
                })
            }
            None => return Err(malformed("sideCondition is absent")),
        };

        Ok(Self {
            digest: plan_digest,
            event_vocabulary_digest: vocabulary_digest,
            variables,
            arms,
            side_condition,
            vocabulary: vocabulary.clone(),
        })
    }
}

/// A digest-checked named query. Entry/exported names are preserved opaque strings.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct NamedQuery {
    pub pattern_source: ArtifactRef,
    pub pattern_plan: ArtifactRef,
    pub entry_module: String,
    pub exported_name: String,
    pub query_id: Digest,
}

impl NamedQuery {
    pub fn from_json(value: &SemanticJson, plan: &PatternPlan) -> Result<Self, PatternFailure> {
        let fields = exact_object(
            value,
            &[
                "patternSource",
                "patternPlan",
                "entryModule",
                "exportedName",
                "queryId",
            ],
            "pattern query",
        )?;
        let pattern_source = parse_artifact(fields.get("patternSource"), "pattern-source")?;
        let pattern_plan = parse_artifact(fields.get("patternPlan"), "pattern-plan")?;
        if pattern_plan.digest != plan.digest {
            return Err(PatternFailure::new(
                PatternFailureKind::QueryPlanMismatch,
                "query does not bind the supplied plan",
            ));
        }
        let query_id = parsed_digest(fields.get("queryId"), "queryId")?;
        let expected = digest_without_field(
            &DigestDomain::new("k-in-k/pattern-query/v1").expect("static domain"),
            value,
            "queryId",
        )
        .map_err(|_| malformed("query self-ID projection failed"))?;
        if query_id != expected {
            return Err(PatternFailure::new(
                PatternFailureKind::QueryIdentity,
                "queryId does not cover the exact source/plan/name record",
            ));
        }
        Ok(Self {
            pattern_source,
            pattern_plan,
            entry_module: nonempty(
                text(fields.get("entryModule"), "entryModule")?,
                "entryModule",
            )?,
            exported_name: nonempty(
                text(fields.get("exportedName"), "exportedName")?,
                "exportedName",
            )?,
            query_id,
        })
    }
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum SideConditionResult {
    True,
    False,
    Unknown,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SideConditionRow {
    pub condition_digest: Digest,
    pub bindings_digest: Digest,
    pub path_predicate_digest: Digest,
    pub result: SideConditionResult,
}

/// Exact finite table lookup; a missing row returns unknown.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SideConditionTable {
    pub digest: Digest,
    rows: BTreeMap<(Digest, Digest, Digest), SideConditionResult>,
}

impl SideConditionTable {
    pub fn new(expected: Digest, rows: Vec<SideConditionRow>) -> Result<Self, PatternFailure> {
        let mut previous = None;
        let mut map = BTreeMap::new();
        for row in &rows {
            let key = (
                row.condition_digest.clone(),
                row.bindings_digest.clone(),
                row.path_predicate_digest.clone(),
            );
            if previous.as_ref().is_some_and(|old| old >= &key)
                || map.insert(key.clone(), row.result).is_some()
            {
                return Err(PatternFailure::new(
                    PatternFailureKind::InvalidSideTable,
                    "side-condition rows must be unique and canonically ordered",
                ));
            }
            previous = Some(key);
        }
        let value = object([
            ("schemaVersion", SemanticJson::Integer(1)),
            ("tableDigest", string(expected.as_str())),
            (
                "rows",
                SemanticJson::Array(rows.iter().map(SideConditionRow::to_json).collect()),
            ),
        ]);
        let actual = digest_without_field(
            &DigestDomain::new("k-in-k/side-condition-conformance-table/v1")
                .expect("static domain"),
            &value,
            "tableDigest",
        )
        .map_err(|_| malformed("side table self-ID projection failed"))?;
        if actual != expected {
            return Err(PatternFailure::new(
                PatternFailureKind::SideTableIdentity,
                "side-condition table digest drift",
            ));
        }
        Ok(Self {
            digest: expected,
            rows: map,
        })
    }

    fn lookup(
        &self,
        condition: &Digest,
        bindings: &Digest,
        predicate: &Digest,
    ) -> SideConditionResult {
        self.rows
            .get(&(condition.clone(), bindings.clone(), predicate.clone()))
            .copied()
            .unwrap_or(SideConditionResult::Unknown)
    }
}

impl SideConditionRow {
    fn to_json(&self) -> SemanticJson {
        object([
            (
                "condition",
                object([
                    ("role", string("pattern-side-condition")),
                    ("digest", string(self.condition_digest.as_str())),
                ]),
            ),
            ("bindingsDigest", string(self.bindings_digest.as_str())),
            (
                "pathPredicateDigest",
                string(self.path_predicate_digest.as_str()),
            ),
            (
                "result",
                string(match self.result {
                    SideConditionResult::True => "true",
                    SideConditionResult::False => "false",
                    SideConditionResult::Unknown => "unknown",
                }),
            ),
        ])
    }
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Event {
    pub index: usize,
    pub constructor: String,
    pub payload: Vec<Term>,
    pub origin: EventOrigin,
    pub transition_ordinal: u64,
    pub emission_ordinal: u64,
}

/// One concrete semantic-site origin resolved from an observation manifest.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct SemanticSiteOrigin {
    pub site_id: Digest,
    pub role: String,
    pub term_path: SemanticJson,
}

/// Complete portable emitting-sentence provenance and its optional semantic site.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EventOrigin {
    pub emitting_sentence: Provenance,
    pub semantic_site: Option<SemanticSiteOrigin>,
}

/// One definition-owned application signature used to seed a trace graph.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermSignature {
    pub label: String,
    pub result_sort: String,
    pub argument_sorts: Vec<String>,
}

/// Closed execution terminal kinds carried by a trace.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum ExecutionTerminalKind {
    Normal,
    Stuck,
    SemanticCrash,
}

/// A role-typed terminal key. Its semantic roots are resolved through `EvaluationAuthority`.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionTerminal {
    pub kind: ExecutionTerminalKind,
    pub artifact: ArtifactRef,
}

/// Independently resolved semantic roots for one terminal or crash artifact.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TerminalAuthority {
    pub kind: ExecutionTerminalKind,
    pub definition_digest: Digest,
    pub execution_profile_digest: Option<Digest>,
}

/// Exact finite bounds included in the portable pattern result.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ExecutionBounds {
    pub depth: Option<u64>,
    pub time_ms: Option<u64>,
    pub branches: Option<u64>,
    pub results: Option<u64>,
}

/// Definition, observation, terminal, signature, variable, and bounds roots resolved outside a trace.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EvaluationAuthority {
    pub definition_digest: Digest,
    pub test_id: String,
    pub observer_digest: Digest,
    pub observer_version: u64,
    pub execution_profile_digest: Digest,
    pub bounds: ExecutionBounds,
    pub trace_constructors: BTreeMap<String, Constructor>,
    pub provenance_by_lineage: BTreeMap<Digest, Provenance>,
    pub signatures: BTreeMap<Digest, TermSignature>,
    pub variables_by_path: BTreeMap<Digest, BTreeMap<String, String>>,
    pub terminals: BTreeMap<Digest, TerminalAuthority>,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct TermRelation {
    pub left: Term,
    pub right: Term,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum PathStop {
    Terminal,
    Stuck,
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
        matches!(self, Self::Terminal | Self::Stuck)
    }
}

/// Actual execution termination, kept distinct from the query-level match stop.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum ExecutionStop {
    Terminal,
    Stuck,
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
    pub definition_digest: Digest,
    pub test_id: String,
    pub path_ordinal: usize,
    pub path_key: Option<String>,
    pub path_identity_digest: Digest,
    pub trace_digest: Digest,
    pub complete: bool,
    pub stop: PathStop,
    pub execution_stop: ExecutionStop,
    pub execution_terminal: Option<ExecutionTerminal>,
    pub events: Vec<Event>,
    pub path_predicate: Term,
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
    Error,
}

/// Explicit finite collection evidence. Empty clean exhaustion requires a decision key.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CollectionEvidence {
    pub stop: CollectionStop,
    pub pending_work: u64,
    pub empty_search_decision: Option<ArtifactRef>,
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

/// Exact query-level options for one portable evaluation.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct EvaluationOptions {
    /// Without stable keys, paths are told apart only by their identity digest, so two
    /// paths with identical traces are rejected rather than counted twice or coalesced.
    /// Coalescing is unsound because equivalences and inequalities are not covered by the
    /// identity digest: two paths with one identity can still evaluate differently.
    pub stable_path_keys: bool,
    pub search_policy: SearchPolicy,
    pub input_error: bool,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Witness {
    pub path_ordinal: usize,
    pub path_key: Option<String>,
    pub replay_key: Option<Digest>,
    pub arm_ordinal: usize,
    pub event_indices: Vec<usize>,
    pub events: Vec<Event>,
    pub bindings: Vec<Binding>,
    pub path_predicate: Term,
    pub stop_reason: PathStop,
    pub execution_stop_reason: ExecutionStop,
}

#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Evaluation {
    pub outcome: PatternOutcome,
    pub complete_coverage: bool,
    pub witnesses: Vec<Witness>,
    pub primary_witness: Option<usize>,
    /// For `Unknown`, the least severe incomplete stop in `PathStop` order. Unlike
    /// `CorpusDecision::cause`, this does not prefer an error over a limit.
    pub failure: Option<PathStop>,
    pub search_policy: SearchPolicy,
    pub bounds: ExecutionBounds,
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum RelationResult {
    Equal,
    Unequal,
    Indeterminate,
}

struct PendingWitness {
    path_order: String,
    witness: Witness,
}

/// Evaluates a validated plan over supplied finite path-local traces.
pub fn evaluate(
    authority: &EvaluationAuthority,
    plan: &PatternPlan,
    paths: &[PathInput],
    collection: &CollectionEvidence,
    side_table: Option<&SideConditionTable>,
    options: EvaluationOptions,
) -> Result<Evaluation, PatternFailure> {
    let EvaluationOptions {
        stable_path_keys,
        search_policy,
        input_error,
    } = options;
    validate_authority(authority)?;
    if input_error {
        return Ok(Evaluation {
            outcome: PatternOutcome::Error,
            complete_coverage: false,
            witnesses: Vec::new(),
            primary_witness: None,
            failure: Some(PathStop::Error),
            search_policy,
            bounds: authority.bounds.clone(),
        });
    }
    validate_collection(paths, collection, search_policy)?;
    let mut keyed = BTreeSet::new();
    let mut unkeyed = BTreeSet::new();
    let mut path_ordinals = BTreeSet::new();
    for path in paths {
        validate_path_roots(path, authority, plan)?;
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
        } else if !unkeyed.insert(path.path_identity_digest.clone()) {
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
    for path in paths {
        let path_order = path
            .path_key
            .clone()
            .unwrap_or_else(|| path.path_identity_digest.to_string());
        for (arm_ordinal, arm) in plan.arms.iter().enumerate() {
            let mut context = ExtendContext {
                test_id: &authority.test_id,
                plan,
                path,
                arm,
                arm_ordinal,
                side_table,
                path_order: &path_order,
                pending: &mut pending,
                indeterminate: &mut indeterminate,
            };
            extend_occurrence(&mut context, 0, &[], &BTreeMap::new());
        }
    }
    pending.sort_by(|left, right| {
        left.path_order
            .cmp(&right.path_order)
            .then_with(|| left.witness.event_indices.cmp(&right.witness.event_indices))
            .then_with(|| {
                binding_digest(&left.witness.bindings).cmp(&binding_digest(&right.witness.bindings))
            })
            .then_with(|| left.witness.arm_ordinal.cmp(&right.witness.arm_ordinal))
    });
    let witnesses = pending
        .into_iter()
        .map(|item| item.witness)
        .collect::<Vec<_>>();
    if search_policy == SearchPolicy::ExistentialFirst {
        // `validate_collection` admits at most one match-found path; an indeterminate
        // candidate on it is missing evidence, not a dishonest stop.
        let stopped = paths.iter().any(|path| path.stop == PathStop::MatchFound);
        if witnesses
            .iter()
            .any(|witness| witness.stop_reason != PathStop::MatchFound)
            || (stopped && witnesses.is_empty() && !indeterminate)
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
        paths
            .iter()
            .filter(|path| !path.complete)
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
        bounds: authority.bounds.clone(),
    })
}

fn validate_authority(authority: &EvaluationAuthority) -> Result<(), PatternFailure> {
    if authority.test_id.is_empty() {
        return Err(PatternFailure::new(
            PatternFailureKind::InputError,
            "test identity must be nonempty",
        ));
    }
    if authority.bounds.time_ms == Some(0)
        || authority.bounds.branches == Some(0)
        || authority.bounds.results == Some(0)
    {
        return Err(PatternFailure::new(
            PatternFailureKind::BoundsMismatch,
            "time, branch, and result bounds must be positive when present",
        ));
    }
    if authority
        .provenance_by_lineage
        .iter()
        .any(|(lineage, provenance)| lineage != &provenance.lineage_id)
    {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidOrigin,
            "provenance registry key differs from its complete lineage root",
        ));
    }
    if authority.signatures.values().any(|signature| {
        signature.label.is_empty()
            || signature.result_sort.is_empty()
            || signature.argument_sorts.iter().any(String::is_empty)
    }) {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidTermGraph,
            "definition signature roots contain an empty label or sort",
        ));
    }
    if authority
        .trace_constructors
        .iter()
        .any(|(name, constructor)| {
            name.is_empty()
                || name != &constructor.name
                || constructor.payload_sorts.iter().any(String::is_empty)
        })
    {
        return Err(PatternFailure::new(
            PatternFailureKind::UnknownConstructor,
            "trace constructor authority contains an invalid name or payload sort",
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
        let Some(decision) = &collection.empty_search_decision else {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidCollection,
                "empty clean exhaustion requires an empty-search decision",
            ));
        };
        if decision.role != "empty-search-decision" {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidCollection,
                "empty-search decision has the wrong artifact role",
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

fn validate_path_roots(
    path: &PathInput,
    authority: &EvaluationAuthority,
    plan: &PatternPlan,
) -> Result<(), PatternFailure> {
    if path.definition_digest != authority.definition_digest || path.test_id != authority.test_id {
        return Err(PatternFailure::new(
            PatternFailureKind::DefinitionMismatch,
            "trace definition or test root differs from the evaluation authority",
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
    if let Some(terminal) = &path.execution_terminal {
        let expected_role = match terminal.kind {
            ExecutionTerminalKind::Normal | ExecutionTerminalKind::Stuck => "terminal-state",
            ExecutionTerminalKind::SemanticCrash => "semantic-crash",
        };
        let Some(resolved) = authority.terminals.get(&terminal.artifact.digest) else {
            return Err(PatternFailure::new(
                PatternFailureKind::TerminalMismatch,
                "trace terminal artifact is unresolved",
            ));
        };
        if terminal.artifact.role != expected_role
            || resolved.kind != terminal.kind
            || resolved.definition_digest != path.definition_digest
            || (terminal.kind == ExecutionTerminalKind::SemanticCrash
                && resolved.execution_profile_digest.as_ref()
                    != Some(&authority.execution_profile_digest))
            || (terminal.kind != ExecutionTerminalKind::SemanticCrash
                && resolved.execution_profile_digest.is_some())
        {
            return Err(PatternFailure::new(
                PatternFailureKind::TerminalMismatch,
                "terminal role, kind, definition, or execution-profile root drifted",
            ));
        }
    }

    validate_relations(path)?;
    validate_events(path, plan, authority)?;
    let Some(expected_variables) = authority.variables_by_path.get(&path.path_identity_digest)
    else {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidTermGraph,
            "path has no independently resolved variable graph root",
        ));
    };
    let mut variables = BTreeMap::new();
    validate_term(&path.path_predicate, &authority.signatures, &mut variables)?;
    if path.path_predicate.sort != "Bool" {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidTermGraph,
            "path predicate must have sort Bool",
        ));
    }
    for event in &path.events {
        for term in &event.payload {
            validate_term(term, &authority.signatures, &mut variables)?;
        }
    }
    for relation in path.equivalences.iter().chain(&path.inequalities) {
        if relation.left.sort != relation.right.sort {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidTermGraph,
                "supplied relation connects terms of different sorts",
            ));
        }
        validate_term(&relation.left, &authority.signatures, &mut variables)?;
        validate_term(&relation.right, &authority.signatures, &mut variables)?;
    }
    if &variables != expected_variables {
        return Err(PatternFailure::new(
            PatternFailureKind::InvalidTermGraph,
            "derived path variable graph differs from its independently resolved root",
        ));
    }

    let expected_identity = derive_path_identity(path)?;
    if path.path_identity_digest != expected_identity {
        return Err(invalid_path(
            "path identity does not cover the complete schedule-independent trace",
        ));
    }
    let expected_trace = derive_trace_digest(path)?;
    if path.trace_digest != expected_trace {
        return Err(invalid_path(
            "trace digest does not cover the complete validated trace",
        ));
    }
    Ok(())
}

fn validate_events(
    path: &PathInput,
    plan: &PatternPlan,
    authority: &EvaluationAuthority,
) -> Result<(), PatternFailure> {
    let mut previous_transition = None;
    let mut expected_emission = 0;
    for (index, event) in path.events.iter().enumerate() {
        if event.index != index {
            return Err(invalid_path(
                "event indices must be zero-based and contiguous",
            ));
        }
        let Some(constructor) = authority.trace_constructors.get(&event.constructor) else {
            return Err(PatternFailure::new(
                PatternFailureKind::UnknownConstructor,
                format!("trace contains unknown constructor {}", event.constructor),
            ));
        };
        if let Some(plan_constructor) = plan.vocabulary.constructor(&event.constructor)
            && plan_constructor != constructor
        {
            return Err(PatternFailure::new(
                PatternFailureKind::VocabularyIdentity,
                "trace constructor authority differs from the plan vocabulary",
            ));
        }
        if event.payload.len() != constructor.payload_sorts.len()
            || event
                .payload
                .iter()
                .zip(&constructor.payload_sorts)
                .any(|(term, sort)| &term.sort != sort)
        {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidPayload,
                "known trace event payload arity or sort differs from the vocabulary",
            ));
        }
        let provenance = &event.origin.emitting_sentence;
        if authority.provenance_by_lineage.get(&provenance.lineage_id) != Some(provenance) {
            return Err(PatternFailure::new(
                PatternFailureKind::InvalidOrigin,
                "event provenance is unresolved or differs from the definition root",
            ));
        }
        match (constructor.origin_mode, &event.origin.semantic_site) {
            (OriginMode::EmittingSentence, None) => {}
            (OriginMode::EmittingSentenceAndSemanticSite, Some(site)) => {
                validate_semantic_path(&site.term_path)?;
                if site.role.is_empty() {
                    return Err(PatternFailure::new(
                        PatternFailureKind::InvalidOrigin,
                        "semantic-site role must be nonempty",
                    ));
                }
                let expected_site = checked_domain_digest(
                    "k-in-k/observation-site/v1",
                    &object([
                        ("observerDigest", string(authority.observer_digest.as_str())),
                        (
                            "observerVersion",
                            SemanticJson::Integer(
                                i64::try_from(authority.observer_version)
                                    .map_err(|_| invalid_origin("observer version exceeds i64"))?,
                            ),
                        ),
                        (
                            "definitionDigest",
                            string(authority.definition_digest.as_str()),
                        ),
                        ("targetLineage", string(provenance.lineage_id.as_str())),
                        ("role", string(&site.role)),
                        ("termPath", site.term_path.clone()),
                    ]),
                    PatternFailureKind::InvalidOrigin,
                )?;
                if site.site_id != expected_site {
                    return Err(invalid_origin(
                        "semantic-site identity does not cover its observation roots",
                    ));
                }
            }
            _ => {
                return Err(invalid_origin(
                    "event origin mode disagrees with semantic-site presence",
                ));
            }
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

struct ExtendContext<'a> {
    test_id: &'a str,
    plan: &'a PatternPlan,
    path: &'a PathInput,
    arm: &'a PatternArm,
    arm_ordinal: usize,
    side_table: Option<&'a SideConditionTable>,
    path_order: &'a str,
    pending: &'a mut Vec<PendingWitness>,
    indeterminate: &'a mut bool,
}

fn extend_occurrence(
    context: &mut ExtendContext<'_>,
    atom_ordinal: usize,
    indices: &[usize],
    bindings: &BTreeMap<String, Term>,
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
            let by_name = ordered
                .iter()
                .map(|item| (item.name.as_str(), item))
                .collect::<BTreeMap<_, _>>();
            let inputs = side
                .input_variables
                .iter()
                .map(|name| (*by_name.get(name.as_str()).expect("validated side input")).clone())
                .collect::<Vec<_>>();
            let result = context
                .side_table
                .map_or(SideConditionResult::Unknown, |table| {
                    table.lookup(
                        &side.artifact.digest,
                        &binding_digest(&inputs),
                        &domain_digest(
                            "k-in-k/path-predicate/v1",
                            &context.path.path_predicate.to_json(),
                        ),
                    )
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
        let replay_key = context.path.path_key.as_ref().map(|path_key| {
            domain_digest(
                "k-in-k/witness-replay-key/v1",
                &object([
                    ("testId", string(context.test_id)),
                    ("pathKey", string(path_key)),
                    (
                        "eventIndices",
                        SemanticJson::Array(
                            indices
                                .iter()
                                .map(|index| {
                                    SemanticJson::Integer(
                                        i64::try_from(*index).expect("usize fits fixture i64"),
                                    )
                                })
                                .collect(),
                        ),
                    ),
                ]),
            )
        });
        context.pending.push(PendingWitness {
            path_order: context.path_order.to_owned(),
            witness: Witness {
                path_ordinal: context.path.path_ordinal,
                path_key: context.path.path_key.clone(),
                replay_key,
                arm_ordinal: context.arm_ordinal,
                event_indices: indices.to_vec(),
                events: indices
                    .iter()
                    .map(|index| context.path.events[*index].clone())
                    .collect(),
                bindings: ordered,
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
            context.path,
        ) {
            AtomMatch::Matched(next) => {
                let mut next_indices = indices.to_vec();
                next_indices.push(index);
                extend_occurrence(context, atom_ordinal + 1, &next_indices, &next);
            }
            AtomMatch::Indeterminate => *context.indeterminate = true,
            AtomMatch::Mismatch => {}
        }
    }
}

enum AtomMatch {
    Matched(BTreeMap<String, Term>),
    Indeterminate,
    Mismatch,
}

fn match_atom(
    atom: &Atom,
    event: &Event,
    bindings: &BTreeMap<String, Term>,
    path: &PathInput,
) -> AtomMatch {
    if atom.constructor != event.constructor {
        return AtomMatch::Mismatch;
    }
    let mut resolved = bindings.clone();
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
                match term_relation(bound, term, path) {
                    RelationResult::Equal => {}
                    RelationResult::Unequal => return AtomMatch::Mismatch,
                    RelationResult::Indeterminate => return AtomMatch::Indeterminate,
                }
            }
        }
    }
    AtomMatch::Matched(resolved)
}

fn term_relation(left: &Term, right: &Term, path: &PathInput) -> RelationResult {
    if left == right || connected(left, right, &path.equivalences) {
        return RelationResult::Equal;
    }
    if path.inequalities.iter().any(|pair| {
        connected(left, &pair.left, &path.equivalences)
            && connected(right, &pair.right, &path.equivalences)
            || connected(left, &pair.right, &path.equivalences)
                && connected(right, &pair.left, &path.equivalences)
    }) {
        RelationResult::Unequal
    } else if contains_variable(left) || contains_variable(right) {
        RelationResult::Indeterminate
    } else {
        RelationResult::Unequal
    }
}

fn contains_variable(term: &Term) -> bool {
    match &term.node {
        TermNode::Variable { .. } => true,
        TermNode::Application { args, .. } => args.iter().any(contains_variable),
        TermNode::Rewrite { left, right } => contains_variable(left) || contains_variable(right),
        TermNode::Sequence { items } => items.iter().any(contains_variable),
        TermNode::Injection { term, .. } => contains_variable(term),
        TermNode::Token { .. } => false,
    }
}

fn connected(left: &Term, right: &Term, relations: &[TermRelation]) -> bool {
    if left == right {
        return true;
    }
    let mut queue = VecDeque::from([left]);
    let mut visited: Vec<&Term> = Vec::new();
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

fn validate_relations(path: &PathInput) -> Result<(), PatternFailure> {
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

/// Existential aggregation requires an explicit finite-exhaustion witness before absence.
#[must_use]
pub fn aggregate_existential(
    components: &[PatternOutcome],
    global_error: bool,
    exhaustion: Option<&ArtifactRef>,
) -> PatternOutcome {
    if global_error {
        PatternOutcome::Error
    } else if components.contains(&PatternOutcome::Match) {
        PatternOutcome::Match
    } else if components
        .iter()
        .any(|item| matches!(item, PatternOutcome::Unknown | PatternOutcome::Error))
    {
        PatternOutcome::Unknown
    } else if exhaustion.is_some_and(|item| item.role == "empty-search-decision") {
        PatternOutcome::NoMatch
    } else if exhaustion.is_some() {
        PatternOutcome::Error
    } else {
        PatternOutcome::Unknown
    }
}

/// One corpus test in manifest order: evaluated to an outcome, or explicitly skipped.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CorpusComponent {
    Evaluated(PatternOutcome),
    Skipped(CorpusSkip),
}

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CorpusSkip {
    SharedSetupFailed,
    MatchFound,
}

/// The folded corpus answer. Indices refer to manifest test order.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CorpusDecision {
    pub outcome: PatternOutcome,
    pub complete_coverage: bool,
    pub matching_tests: Vec<usize>,
    /// First test-scoped error, else first unknown, that makes the corpus inconclusive.
    /// Unlike `Evaluation::failure`, an error is never hidden behind an earlier unknown.
    pub cause: Option<usize>,
}

/// Folds per-test outcomes after checking that every skip is justified: a shared-setup
/// failure skips every test, and early stop skips exactly the tests after the first match.
/// Absence follows `aggregate_existential`, so it needs explicit exhaustion evidence.
/// Corpus-scoped Error arises only from shared-setup failure; a test-scoped Error leaves
/// the corpus Unknown and never overrides a Match, as a path-local error stop does in
/// `evaluate`.
pub fn aggregate_corpus(
    components: &[CorpusComponent],
    shared_setup_failed: bool,
    early_stop_after_match: bool,
    exhaustion: Option<&ArtifactRef>,
) -> Result<CorpusDecision, PatternFailure> {
    let invalid = |detail: &str| {
        Err(PatternFailure::new(
            PatternFailureKind::InvalidCorpus,
            detail,
        ))
    };
    if components.is_empty() {
        return invalid("corpus has no tests");
    }
    if exhaustion.is_some_and(|item| item.role != "empty-search-decision") {
        return invalid("corpus exhaustion artifact has the wrong role");
    }
    let first_match = components
        .iter()
        .position(|item| *item == CorpusComponent::Evaluated(PatternOutcome::Match));
    let expected_skip = |index: usize| {
        if shared_setup_failed {
            Some(CorpusSkip::SharedSetupFailed)
        } else if early_stop_after_match && first_match.is_some_and(|first| index > first) {
            Some(CorpusSkip::MatchFound)
        } else {
            None
        }
    };
    let mut outcomes = Vec::with_capacity(components.len());
    for (index, component) in components.iter().enumerate() {
        match (*component, expected_skip(index)) {
            (CorpusComponent::Evaluated(outcome), None) => outcomes.push(outcome),
            (CorpusComponent::Skipped(skip), Some(expected)) if skip == expected => {}
            _ => return invalid("corpus skips do not follow its setup and stop policy"),
        }
    }
    let outcome = aggregate_existential(&outcomes, shared_setup_failed, exhaustion);
    let first = |wanted| {
        components
            .iter()
            .position(|item| *item == CorpusComponent::Evaluated(wanted))
    };
    let cause = matches!(outcome, PatternOutcome::Unknown | PatternOutcome::Error)
        .then(|| first(PatternOutcome::Error).or_else(|| first(PatternOutcome::Unknown)))
        .flatten();
    Ok(CorpusDecision {
        outcome,
        complete_coverage: matches!(outcome, PatternOutcome::Match | PatternOutcome::NoMatch)
            && outcomes.len() == components.len()
            && outcomes
                .iter()
                .all(|item| matches!(item, PatternOutcome::Match | PatternOutcome::NoMatch)),
        matching_tests: components
            .iter()
            .enumerate()
            .filter(|(_, item)| **item == CorpusComponent::Evaluated(PatternOutcome::Match))
            .map(|(index, _)| index)
            .collect(),
        cause,
    })
}

fn binding_digest(bindings: &[Binding]) -> Digest {
    domain_digest(
        "k-in-k/bindings/v1",
        &SemanticJson::Array(
            bindings
                .iter()
                .map(|binding| {
                    object([
                        ("name", string(&binding.name)),
                        ("term", binding.term.to_json()),
                    ])
                })
                .collect(),
        ),
    )
}

/// Rederives the schedule-independent v1 path identity from the complete trace payload.
pub fn derive_path_identity(path: &PathInput) -> Result<Digest, PatternFailure> {
    checked_domain_digest(
        "k-in-k/unkeyed-path/v1",
        &path_identity_payload(path)?,
        PatternFailureKind::InvalidPath,
    )
}

/// Rederives the exact v1 event-trace digest, including the checked path identity.
pub fn derive_trace_digest(path: &PathInput) -> Result<Digest, PatternFailure> {
    checked_domain_digest(
        "k-in-k/event-trace/v1",
        &path_json(path)?,
        PatternFailureKind::InvalidPath,
    )
}

fn path_identity_payload(path: &PathInput) -> Result<SemanticJson, PatternFailure> {
    Ok(object([
        ("schemaVersion", SemanticJson::Integer(1)),
        ("definitionDigest", string(path.definition_digest.as_str())),
        ("testId", string(&path.test_id)),
        ("pathPredicate", path.path_predicate.to_json()),
        ("complete", SemanticJson::Bool(path.complete)),
        ("stopReason", string(path.execution_stop.as_str())),
        (
            "executionTerminal",
            execution_terminal_json(&path.execution_terminal),
        ),
        (
            "events",
            SemanticJson::Array(
                path.events
                    .iter()
                    .map(event_json)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        ),
    ]))
}

fn path_json(path: &PathInput) -> Result<SemanticJson, PatternFailure> {
    Ok(object([
        ("schemaVersion", SemanticJson::Integer(1)),
        ("definitionDigest", string(path.definition_digest.as_str())),
        ("testId", string(&path.test_id)),
        (
            "pathOrdinal",
            checked_integer(path.path_ordinal, "path ordinal")?,
        ),
        (
            "pathKey",
            path.path_key
                .as_ref()
                .map_or(SemanticJson::Null, |value| string(value)),
        ),
        (
            "pathIdentityDigest",
            string(path.path_identity_digest.as_str()),
        ),
        ("pathPredicate", path.path_predicate.to_json()),
        ("complete", SemanticJson::Bool(path.complete)),
        ("stopReason", string(path.execution_stop.as_str())),
        (
            "executionTerminal",
            execution_terminal_json(&path.execution_terminal),
        ),
        (
            "events",
            SemanticJson::Array(
                path.events
                    .iter()
                    .map(event_json)
                    .collect::<Result<Vec<_>, _>>()?,
            ),
        ),
    ]))
}

fn event_json(event: &Event) -> Result<SemanticJson, PatternFailure> {
    Ok(object([
        ("index", checked_integer(event.index, "event index")?),
        (
            "transitionOrdinal",
            checked_u64(event.transition_ordinal, "transition ordinal")?,
        ),
        (
            "emissionOrdinal",
            checked_u64(event.emission_ordinal, "emission ordinal")?,
        ),
        ("constructor", string(&event.constructor)),
        (
            "payload",
            SemanticJson::Array(event.payload.iter().map(Term::to_json).collect()),
        ),
        (
            "origin",
            object([
                ("emittingSentence", event.origin.emitting_sentence.to_json()),
                (
                    "semanticSite",
                    event
                        .origin
                        .semantic_site
                        .as_ref()
                        .map_or(SemanticJson::Null, |site| {
                            object([
                                ("siteId", string(site.site_id.as_str())),
                                ("role", string(&site.role)),
                                ("termPath", site.term_path.clone()),
                            ])
                        }),
                ),
            ]),
        ),
    ]))
}

fn execution_terminal_json(terminal: &Option<ExecutionTerminal>) -> SemanticJson {
    terminal.as_ref().map_or(SemanticJson::Null, |terminal| {
        object([
            (
                "kind",
                string(match terminal.kind {
                    ExecutionTerminalKind::Normal => "normal",
                    ExecutionTerminalKind::Stuck => "stuck",
                    ExecutionTerminalKind::SemanticCrash => "semantic-crash",
                }),
            ),
            (
                "artifact",
                object([
                    ("role", string(&terminal.artifact.role)),
                    ("digest", string(terminal.artifact.digest.as_str())),
                ]),
            ),
        ])
    })
}

impl ExecutionStop {
    const fn as_str(self) -> &'static str {
        match self {
            Self::Terminal => "terminal",
            Self::Stuck => "stuck",
            Self::QuerySatisfied => "query-satisfied",
            Self::DepthLimit => "depth-limit",
            Self::TimeLimit => "time-limit",
            Self::BranchLimit => "branch-limit",
            Self::ResultLimit => "result-limit",
            Self::ResourceLimit => "resource-limit",
            Self::SolverUnknown => "solver-unknown",
            Self::BackendLimit => "error",
            Self::Error => "error",
        }
    }
}

fn validate_term(
    term: &Term,
    signatures: &BTreeMap<Digest, TermSignature>,
    variables: &mut BTreeMap<String, String>,
) -> Result<(), PatternFailure> {
    if term.sort.is_empty() {
        return Err(invalid_term("term sort must be nonempty"));
    }
    match &term.node {
        TermNode::Token { .. } => {}
        TermNode::Variable { name } => {
            if name.is_empty() {
                return Err(invalid_term("term variable name must be nonempty"));
            }
            if let Some(previous) = variables.insert(name.clone(), term.sort.clone())
                && previous != term.sort
            {
                return Err(invalid_term(
                    "one path variable is used with contradictory sorts",
                ));
            }
        }
        TermNode::Application {
            symbol_id,
            label,
            args,
        } => {
            for argument in args {
                validate_term(argument, signatures, variables)?;
            }
            let actual = TermSignature {
                label: label.clone(),
                result_sort: term.sort.clone(),
                argument_sorts: args.iter().map(|argument| argument.sort.clone()).collect(),
            };
            if signatures.get(symbol_id) != Some(&actual) {
                return Err(invalid_term(
                    "application signature is unresolved or contradicts the definition root",
                ));
            }
        }
        TermNode::Rewrite { left, right } => {
            validate_term(left, signatures, variables)?;
            validate_term(right, signatures, variables)?;
            if left.sort != right.sort || left.sort != term.sort {
                return Err(invalid_term(
                    "rewrite wrapper and children must have one exact sort",
                ));
            }
        }
        TermNode::Sequence { items } => {
            for item in items {
                validate_term(item, signatures, variables)?;
            }
        }
        TermNode::Injection {
            from_sort,
            to_sort,
            term: child,
        } => {
            validate_term(child, signatures, variables)?;
            if from_sort.is_empty()
                || to_sort.is_empty()
                || child.sort != *from_sort
                || term.sort != *to_sort
            {
                return Err(invalid_term(
                    "injection sorts disagree with its child or wrapper",
                ));
            }
        }
    }
    Ok(())
}

fn validate_semantic_path(value: &SemanticJson) -> Result<(), PatternFailure> {
    let Some(steps) = value.as_array() else {
        return Err(invalid_origin("semantic-site term path must be an array"));
    };
    if steps.is_empty() {
        return Err(invalid_origin("semantic-site term path must be nonempty"));
    }
    for step in steps {
        let Some(fields) = step.as_object() else {
            return Err(invalid_origin("semantic-site path step must be an object"));
        };
        match fields.get("kind").and_then(SemanticJson::as_str) {
            Some("field") if fields.len() == 2 => {
                match fields.get("name").and_then(SemanticJson::as_str) {
                    Some(
                        "sentence" | "body" | "lhs" | "rhs" | "requires" | "ensures" | "attributes",
                    ) => {}
                    _ => {
                        return Err(invalid_origin(
                            "semantic-site field step has an invalid name",
                        ));
                    }
                }
            }
            Some("argument" | "sequence-item") if fields.len() == 2 => {
                if fields
                    .get("index")
                    .and_then(SemanticJson::as_i64)
                    .is_none_or(|item| item < 0)
                {
                    return Err(invalid_origin(
                        "semantic-site indexed step has an invalid index",
                    ));
                }
            }
            Some("injection-term") if fields.len() == 1 => {}
            Some("attribute") if fields.len() == 2 => {
                if fields
                    .get("name")
                    .and_then(SemanticJson::as_str)
                    .is_none_or(str::is_empty)
                {
                    return Err(invalid_origin(
                        "semantic-site attribute name must be nonempty",
                    ));
                }
            }
            _ => {
                return Err(invalid_origin(
                    "semantic-site path step is unsupported or open",
                ));
            }
        }
    }
    Ok(())
}

fn checked_integer(value: usize, field: &str) -> Result<SemanticJson, PatternFailure> {
    i64::try_from(value)
        .map(SemanticJson::Integer)
        .map_err(|_| invalid_path(format!("{field} exceeds i64")))
}

fn checked_u64(value: u64, field: &str) -> Result<SemanticJson, PatternFailure> {
    i64::try_from(value)
        .map(SemanticJson::Integer)
        .map_err(|_| invalid_path(format!("{field} exceeds i64")))
}

fn checked_domain_digest(
    domain: &str,
    value: &SemanticJson,
    kind: PatternFailureKind,
) -> Result<Digest, PatternFailure> {
    digest(
        &DigestDomain::new(domain).expect("static digest domain"),
        value,
    )
    .map_err(|error| PatternFailure::new(kind, format!("invalid semantic value: {error}")))
}

fn parse_artifact(
    value: Option<&SemanticJson>,
    expected_role: &str,
) -> Result<ArtifactRef, PatternFailure> {
    let fields = exact_object(
        value.ok_or_else(|| malformed("artifact reference is absent"))?,
        &["role", "digest"],
        "artifact reference",
    )?;
    let role = text(fields.get("role"), "artifact role")?.to_owned();
    if role != expected_role {
        return Err(malformed(format!("artifact role must be {expected_role}")));
    }
    Ok(ArtifactRef {
        role,
        digest: parsed_digest(fields.get("digest"), "artifact digest")?,
    })
}

fn exact_object<'a>(
    value: &'a SemanticJson,
    fields: &[&str],
    context: &str,
) -> Result<&'a BTreeMap<String, SemanticJson>, PatternFailure> {
    let Some(object) = value.as_object() else {
        return Err(malformed(format!("{context} must be an object")));
    };
    if object.len() != fields.len() || fields.iter().any(|field| !object.contains_key(*field)) {
        return Err(malformed(format!(
            "{context} has missing or unknown fields"
        )));
    }
    Ok(object)
}

fn array<'a>(
    value: Option<&'a SemanticJson>,
    field: &str,
) -> Result<&'a [SemanticJson], PatternFailure> {
    value
        .and_then(SemanticJson::as_array)
        .ok_or_else(|| malformed(format!("{field} must be an array")))
}

fn text<'a>(value: Option<&'a SemanticJson>, field: &str) -> Result<&'a str, PatternFailure> {
    value
        .and_then(SemanticJson::as_str)
        .ok_or_else(|| malformed(format!("{field} must be a string")))
}

fn integer(value: Option<&SemanticJson>, field: &str) -> Result<i64, PatternFailure> {
    value
        .and_then(SemanticJson::as_i64)
        .ok_or_else(|| malformed(format!("{field} must be an integer")))
}

fn parsed_digest(value: Option<&SemanticJson>, field: &str) -> Result<Digest, PatternFailure> {
    Digest::parse(text(value, field)?).map_err(|_| malformed(format!("{field} is not a digest")))
}

fn nonempty(value: &str, field: &str) -> Result<String, PatternFailure> {
    if value.is_empty() {
        Err(malformed(format!("{field} must be nonempty")))
    } else {
        Ok(value.to_owned())
    }
}

fn valid_binding_name(value: &str) -> bool {
    let mut bytes = value.bytes();
    matches!(bytes.next(), Some(b'A'..=b'Z'))
        && bytes.all(|byte| byte.is_ascii_alphanumeric() || byte == b'_')
}

fn malformed(detail: impl Into<String>) -> PatternFailure {
    PatternFailure::new(PatternFailureKind::MalformedPlan, detail)
}

fn invalid_path(detail: impl Into<String>) -> PatternFailure {
    PatternFailure::new(PatternFailureKind::InvalidPath, detail)
}

fn invalid_origin(detail: impl Into<String>) -> PatternFailure {
    PatternFailure::new(PatternFailureKind::InvalidOrigin, detail)
}

fn invalid_term(detail: impl Into<String>) -> PatternFailure {
    PatternFailure::new(PatternFailureKind::InvalidTermGraph, detail)
}

fn collection_failure(stop: CollectionStop) -> Option<PathStop> {
    match stop {
        CollectionStop::SearchExhausted | CollectionStop::MatchFound => None,
        CollectionStop::DepthLimit => Some(PathStop::DepthLimit),
        CollectionStop::TimeLimit => Some(PathStop::TimeLimit),
        CollectionStop::BranchLimit => Some(PathStop::BranchLimit),
        CollectionStop::ResultLimit => Some(PathStop::ResultLimit),
        CollectionStop::ResourceLimit => Some(PathStop::ResourceLimit),
        CollectionStop::SolverUnknown => Some(PathStop::SolverUnknown),
        CollectionStop::BackendLimit => Some(PathStop::BackendLimit),
        CollectionStop::Error => Some(PathStop::Error),
    }
}

fn string(value: &str) -> SemanticJson {
    SemanticJson::String(value.to_owned())
}

fn object<const N: usize>(items: [(&str, SemanticJson); N]) -> SemanticJson {
    SemanticJson::Object(
        items
            .into_iter()
            .map(|(key, value)| (key.to_owned(), value))
            .collect(),
    )
}

fn domain_digest(domain: &str, value: &SemanticJson) -> Digest {
    digest(
        &DigestDomain::new(domain).expect("static digest domain"),
        value,
    )
    .expect("validated pattern inputs form semantic JSON")
}
