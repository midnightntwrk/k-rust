//! ```toml algorithm-site
//! id = "backend.rewrite.execute"
//! role = "part"
//! sites = ["Backend::execute_using"]
//! ```
//!
//! One orchestration path for the CLI, RPC server, and JavaScript hosts: a session, one solver per module, and execution, search, simplification, implication, and proving operations. `wire` contains the JavaScript JSON contracts.

use std::{
    collections::{BTreeMap, BTreeSet},
    fmt,
    sync::Arc,
    time::Duration,
};

#[cfg(not(feature = "z3-inference"))]
use k_rust_backend::smt::NoSolver;
#[cfg(feature = "z3-inference")]
use k_rust_backend::smt::{ModelResult, Z3Options, Z3Solver};
#[cfg(feature = "z3-inference")]
use k_rust_backend::stop;
#[cfg(feature = "z3-inference")]
use k_rust_backend::substitution::Substitution;
use k_rust_backend::{
    definition::{Admission, Admitted, BackendDefinition},
    externalize,
    fresh::RequestNames,
    implication::ImplicationStatus,
    proof::{ProofOptions, ProofSearchOrder, ProofStatus},
    rewrite::{
        ExecutionBranchMode, ExecutionMode, ExecutionOptions, HaltReason, TraceKind,
        execute_observed_with_solver, execute_with_solver,
    },
    rule::ClassifiedAxiom,
    search::{
        SearchOptions, SearchType, search_graph_observed_with_solver, search_graph_with_solver,
        search_paths_observed_with_solver, search_paths_with_solver,
        search_pattern_observed_with_solver, search_pattern_paths_observed_with_solver,
        search_pattern_paths_with_solver, search_pattern_with_solver,
    },
    session::{BackendSession, SessionError},
    simplify::{DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError},
    smt::SmtSolver,
    stop::StopCause,
    term::{Name, Sort},
    transition::ObservationOptions,
};
use serde::{Deserialize, Serialize};
use serde_json::{Value, value::RawValue};

#[cfg(test)]
use k_rust_backend::rule::Predicate;

use crate::kore::{
    ast::Pattern as KorePattern,
    codec as kore_codec,
    parser::{parse_definition, parse_module},
};

pub mod execution;
pub mod implication;
pub mod proving;
pub mod search;
pub mod simplification;
mod wire;
pub use wire::*;

#[derive(Clone, Copy, Debug, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
pub struct BackendOptions {
    pub smt_timeout_ms: u32,
    pub smt_retry_limit: u32,
}

impl Default for BackendOptions {
    fn default() -> Self {
        Self {
            smt_timeout_ms: 125,
            smt_retry_limit: 3,
        }
    }
}

#[derive(Clone, Copy, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct BackendCapabilities {
    pub execution: bool,
    pub simplification: bool,
    pub implication: bool,
    pub model_generation: bool,
    pub proving: bool,
    pub module_addition: bool,
    pub smt: bool,
    pub step_timeouts: bool,
    pub search: bool,
    pub observation: bool,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ExecuteRequest {
    /// A KORE JSON envelope on the wire ([`deserialize_kore_pattern`]).
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub state: KorePattern,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default)]
    pub max_depth: Option<u64>,
    #[serde(default)]
    pub max_breadth: Option<usize>,
    /// Maximum simplifier iterations per rewrite step.
    ///
    /// The bound counts simplification-rule, builtin, and symbolic rewriting. Determined ground
    /// function evaluation (a function equation on a variable-free redex with no residual
    /// condition) runs to its value, bounded only by the step deadline or cancellation and by
    /// the thread's stack, whose exhaustion is a typed error.
    /// Execution keeps a partially simplified term or the original constraints after exhaustion
    /// and records a backend diagnostic before continuing.
    #[serde(default = "wire::default_max_simplification_iterations")]
    pub max_simplification_iterations: usize,
    #[serde(default)]
    pub strategy: ExecutionStrategy,
    #[serde(default)]
    pub stop_at_branch: bool,
    #[serde(default)]
    pub cut_point_rules: Vec<String>,
    #[serde(default)]
    pub terminal_rules: Vec<String>,
    #[serde(default)]
    pub step_timeout_ms: Option<u64>,
    #[serde(default)]
    pub moving_average_timeout: bool,
    /// Assume the initial state's definedness instead of adding it to the path predicate.
    /// Other path obligations still apply: an execution leaf's predicate implies the
    /// definedness of every partial term relied on by its conditions, right-hand sides, and
    /// simplified states in either solver profile.
    #[serde(default)]
    pub assume_state_defined: bool,
    /// `state-set` (the default) merges structurally equal final configurations into one leaf;
    /// `path-set` returns one leaf per explored path, so converging paths keep their own trace,
    /// branch identity, and observations. The result reports the modality it was produced under.
    #[serde(default = "default_result_modality")]
    pub result_modality: ResultModalityOutput,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
}

impl ExecuteRequest {
    /// A request from `state` with every other field at its wire default.
    pub fn new(state: KorePattern) -> Self {
        Self {
            state,
            module_name: None,
            max_depth: None,
            max_breadth: None,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            strategy: ExecutionStrategy::All,
            stop_at_branch: false,
            cut_point_rules: Vec::new(),
            terminal_rules: Vec::new(),
            step_timeout_ms: None,
            moving_average_timeout: false,
            assume_state_defined: false,
            result_modality: ResultModalityOutput::StateSet,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Copy, Debug, Default, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum ExecutionStrategy {
    #[default]
    All,
    Any,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExecutionResult<K = Value> {
    /// Whether `leaves` is a state set (equal configurations merged) or a path set (one leaf
    /// per explored path), as selected by `ExecuteRequest::result_modality`.
    pub modality: ResultModalityOutput,
    pub leaves: Vec<ExecutionLeaf<K>>,
    /// Compatibility copy of the committed effects when execution retains exactly one leaf.
    /// Multi-leaf executions carry their transcripts on the individual leaves.
    pub effects: Vec<EffectOutput>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub discarded: Vec<ObservationEventOutput<K>>,
}

#[derive(Clone, Debug, Deserialize, Serialize)]
#[serde(rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ExecutionLeaf<K = Value> {
    pub state: K,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
    /// Successors reported by a branch or cut-point halt, including each successor's diagnostics.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub candidates: Option<Vec<ExecutionCandidateOutput<K>>>,
    /// The branch's remaining path candidate, when one remains.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub remainder: Option<ExecutionRemainderOutput<K>>,
    pub depth: u64,
    pub reason: HaltReasonOutput,
    /// The rule responsible for an undefined step, when the `Trivial` halt names one.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_id: Option<String>,
    /// The rule's optional label, using the same label as observations and the rule catalog.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub rule_label: Option<String>,
    /// Present on a `Trivial` or `Vacuous` leaf when its emptiness comes from an equation of a
    /// symbol declared `total` (or `functional`) that reduced an application of it to bottom: the
    /// definition contradicts the attribute on that input. A diagnostic about the definition; the
    /// leaf's reason and state are the same with or without it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub contradicted_total: Option<ContradictedTotalOutput<K>>,
    /// The stopped step's structured cause, present exactly for an indeterminate halt.
    /// This uses the same encoding as `IncompleteSearchOutput::Indeterminate.reason`.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub cause: Option<SearchFailureOutput<K>>,
    /// Legacy human-readable diagnostic context.
    ///
    /// This field is not a stable semantic encoding. Consumers must branch on `reason` and use
    /// `cause`, `candidates`, `remainder`, `branch`, and `observations` for structured evidence.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    pub trace: Vec<TraceEntry>,
    /// Committed transition identities, independent of the observation rule filter.
    /// Unobserved execution leaves this empty; an empty allowlist retains every identity.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub branch: Vec<TransitionIdOutput>,
    /// Ordered effects committed on this branch, regardless of observation.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub effects: Vec<EffectOutput>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub observations: Vec<ObservationEventOutput<K>>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ExecutionCandidateOutput<K = Value> {
    pub state: K,
    pub unique_id: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
#[serde(bound(deserialize = "K: Deserialize<'de>"))]
pub struct ExecutionRemainderOutput<K = Value> {
    pub state: K,
    pub rule_ids: Vec<String>,
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub diagnostics: Vec<BackendDiagnosticOutput<K>>,
}

#[derive(Clone, Copy, Debug, Deserialize, Eq, PartialEq, Serialize)]
#[serde(rename_all = "kebab-case")]
pub enum HaltReasonOutput {
    Cancelled,
    /// No ground instance satisfying the leaf's constraint has a rewrite successor.
    /// This does not assert that a satisfying instance exists.
    Stuck,
    /// An undefined step. Under the leaf's constraint some rule applies to every ground
    /// instance: it matches, its `requires` holds, and it blocks the lower priorities. Under
    /// strategy `all`, no instance has a defined successor, because the rule's right-hand side
    /// is undefined there or its `ensures` is false there, and no other applicable rule gives
    /// one. Strategy `any` also offers such instances to every later match of the rule and every
    /// later rule of the same priority, so under it too no rule of that priority gives an
    /// instance a defined successor.
    /// The leaf's state is the configuration before that step, and its constraint is the
    /// condition under which the step is undefined. That constraint may existentially quantify
    /// the rule's fresh variables (`?X`).
    /// The instances' events of that step are not on the leaf's path; an observed run records
    /// them as rolled back in `discarded`.
    /// This does not assert that a satisfying instance exists: the constraint is not checked for
    /// satisfiability, and a consumer that needs to know decides it.
    Trivial,
    /// The path's constraint was shown unsatisfiable, so the leaf has no instance.
    Vacuous,
    Branch,
    CutPoint,
    Terminal,
    DepthBound,
    BreadthBound,
    /// Rule applicability or a remainder could not be decided; no stuckness claim is made.
    Indeterminate,
    UnsupportedHook,
    SimplificationError,
    Timeout,
}

impl HaltReasonOutput {
    pub const ALL: [Self; 13] = [
        Self::Cancelled,
        Self::Stuck,
        Self::Trivial,
        Self::Vacuous,
        Self::Branch,
        Self::CutPoint,
        Self::Terminal,
        Self::DepthBound,
        Self::BreadthBound,
        Self::Indeterminate,
        Self::UnsupportedHook,
        Self::SimplificationError,
        Self::Timeout,
    ];
}

#[derive(Clone, Debug, Deserialize, PartialEq, Serialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct TraceEntry {
    pub depth: u64,
    pub kind: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub label: Option<String>,
    pub unique_id: String,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct PatternRequest {
    /// A KORE JSON envelope on the wire ([`deserialize_kore_pattern`]).
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub state: KorePattern,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
}

impl PatternRequest {
    /// A request from `state` in the default module.
    pub fn new(state: KorePattern) -> Self {
        Self {
            state,
            module_name: None,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ImplicationRequest {
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub antecedent: KorePattern,
    #[serde(deserialize_with = "deserialize_kore_pattern")]
    pub consequent: KorePattern,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
}

impl ImplicationRequest {
    /// A request for `antecedent` implies `consequent` in the default module.
    pub fn new(antecedent: KorePattern, consequent: KorePattern) -> Self {
        Self {
            antecedent,
            consequent,
            module_name: None,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ImplicationResult {
    pub schema_version: u32,
    pub status: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub condition: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub failure: Option<String>,
}

pub const IMPLICATION_SCHEMA_VERSION: u32 = 2;

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ModelResultOutput {
    pub satisfiable: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub substitution: Option<Value>,
    #[serde(skip_serializing_if = "Option::is_none")]
    pub reason: Option<String>,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
pub struct ProveRequest {
    pub module_name: Option<String>,
    pub claim: Option<String>,
    /// Claims available as guarded circularities, selected by label, unique id, or `#index`.
    /// By default the selected claim and every trusted claim are available.
    pub circularities: Option<Vec<String>>,
    pub max_depth: Option<u64>,
    pub min_depth: u64,
    pub breadth_limit: Option<usize>,
    pub max_counterexamples: usize,
    /// Maximum simplifier iterations per proof step, counted as for
    /// `ExecuteRequest::max_simplification_iterations`: determined ground function evaluation
    /// is not counted.
    /// Proof configuration simplification keeps partial terms or original constraints after
    /// exhaustion and records a backend diagnostic before continuing.
    pub max_simplification_iterations: usize,
    pub allow_vacuous: bool,
    pub depth_first: bool,
    pub stuck_check: bool,
    pub step_timeout_ms: Option<u64>,
    pub moving_average_timeout: bool,
    pub schema_version: u32,
}

impl Default for ProveRequest {
    fn default() -> Self {
        Self {
            module_name: None,
            claim: None,
            circularities: None,
            max_depth: None,
            min_depth: 0,
            breadth_limit: None,
            max_counterexamples: 1,
            max_simplification_iterations: DEFAULT_MAX_SIMPLIFICATION_ITERATIONS,
            allow_vacuous: false,
            depth_first: false,
            stuck_check: true,
            step_timeout_ms: None,
            moving_average_timeout: false,
            schema_version: BACKEND_SCHEMA_VERSION,
        }
    }
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofResultOutput<K = Value> {
    pub claim: String,
    pub status: String,
    pub explored_states: u64,
    pub unexplored_states: u64,
    pub leaves: Vec<ProofLeafOutput<K>>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofLeafOutput<K = Value> {
    pub state: K,
    pub depth: u64,
    pub outcome: String,
}

#[derive(Debug)]
pub struct BackendError(pub String);

impl fmt::Display for BackendError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(&self.0)
    }
}

impl std::error::Error for BackendError {}

/// The error of an operation that stopped before producing its answer, for a caller whose
/// error is text: the cause's own text, which names it (`Request cancelled`, the step's timeout,
/// the exhausted stack, `could not initialize Z3: <failure>`). A caller that acts on the cause
/// takes the [`StopCause`] itself through [`Backend::with_solver`]'s `From<StopCause>` bound.
impl From<StopCause> for BackendError {
    #[deny(clippy::wildcard_enum_match_arm)]
    fn from(cause: StopCause) -> Self {
        match cause {
            StopCause::Cancelled
            | StopCause::Deadline(_)
            | StopCause::StackExhausted(_)
            | StopCause::SolverPrelude(_) => Self(cause.to_string()),
        }
    }
}

fn json_output_error(error: serde_json::Error) -> BackendError {
    BackendError(format!("could not serialize backend JSON: {error}"))
}

fn serialize_wire(value: &impl Serialize) -> Result<String, BackendError> {
    serde_json::to_string(value).map_err(json_output_error)
}

/// A persistent backend session over one compiled KORE definition.
pub struct Backend {
    session: BackendSession,
    options: BackendOptions,
    /// The stack the simplifier's recursion may take beyond its thread's in each operation
    /// (`nesting::with_simplification_stack_budget`).
    simplification_stack_budget: usize,
    #[cfg(feature = "z3-inference")]
    solvers: std::collections::BTreeMap<String, Z3Solver>,
    #[cfg(feature = "z3-inference")]
    smt_prelude: Option<String>,
}

impl Backend {
    pub fn new(
        definition_kore: &str,
        module_name: impl Into<String>,
        options: BackendOptions,
    ) -> Result<Self, BackendError> {
        let syntax =
            parse_definition(definition_kore).map_err(error("could not parse KORE definition"))?;
        Self::from_definition(syntax, module_name, options)
    }

    pub fn from_definition(
        syntax: k_rust_kore::kore::ast::Definition,
        module_name: impl Into<String>,
        options: BackendOptions,
    ) -> Result<Self, BackendError> {
        Self::from_session(BackendSession::new(syntax, module_name), options, None)
    }

    /// Internalize one selected module without constructing a solver yet.
    pub fn internalize_definition(
        syntax: &k_rust_kore::kore::ast::Definition,
        module_name: &str,
    ) -> Result<BackendDefinition, BackendError> {
        BackendDefinition::internalize(syntax, module_name)
            .map_err(error("could not internalize KORE definition"))
    }

    /// Internalize a source-compiled definition with the compiler's rewrite order.
    pub fn internalize_source_definition(
        syntax: &k_rust_kore::kore::ast::Definition,
        module_name: &str,
        execution_rewrite_order: &[String],
    ) -> Result<BackendDefinition, BackendError> {
        BackendDefinition::internalize_for_source_execution(
            syntax,
            module_name,
            execution_rewrite_order,
        )
        .map_err(error("could not internalize source execution definition"))
    }

    pub fn from_definition_with_prelude(
        syntax: k_rust_kore::kore::ast::Definition,
        module_name: impl Into<String>,
        options: BackendOptions,
        smt_prelude: String,
    ) -> Result<Self, BackendError> {
        Self::from_session(
            BackendSession::new(syntax, module_name),
            options,
            Some(smt_prelude),
        )
    }

    pub fn from_internalized(
        definition: BackendDefinition,
        options: BackendOptions,
    ) -> Result<Self, BackendError> {
        Self::from_session(BackendSession::with_definition(definition), options, None)
    }

    pub fn from_internalized_with_prelude(
        definition: BackendDefinition,
        options: BackendOptions,
        smt_prelude: Option<String>,
    ) -> Result<Self, BackendError> {
        Self::from_session(
            BackendSession::with_definition(definition),
            options,
            smt_prelude,
        )
    }

    pub fn from_session(
        session: BackendSession,
        options: BackendOptions,
        _smt_prelude: Option<String>,
    ) -> Result<Self, BackendError> {
        let mut backend = Self {
            session,
            options,
            simplification_stack_budget: k_rust_backend::nesting::SIMPLIFICATION_STACK_BUDGET,
            #[cfg(feature = "z3-inference")]
            solvers: Default::default(),
            #[cfg(feature = "z3-inference")]
            smt_prelude: _smt_prelude,
        };
        backend.with_solver(None, |_, _| Ok::<_, BackendError>(()))?;
        Ok(backend)
    }

    /// Set the native stack, in bytes, that the simplifier's recursion may take in each later
    /// operation beyond the stack the operation runs on; the default is
    /// [`k_rust_backend::nesting::SIMPLIFICATION_STACK_BUDGET`]. A function recursion deeper than
    /// that stops with [`StopCause::StackExhausted`]. A smaller budget stops a runaway recursion
    /// sooner and commits less memory before it does; 0 confines the simplifier to the stack the
    /// operation runs on. The budget is per thread; the segments of every thread of the process
    /// together stay within [`k_rust_backend::nesting::SIMPLIFICATION_STACK_PROCESS_BUDGET`].
    pub fn set_simplification_stack_budget(&mut self, bytes: usize) {
        self.simplification_stack_budget = bytes;
    }

    pub fn capabilities(&self) -> BackendCapabilities {
        BackendCapabilities {
            execution: true,
            simplification: true,
            implication: true,
            model_generation: cfg!(feature = "z3-inference"),
            proving: true,
            module_addition: true,
            smt: cfg!(feature = "z3-inference"),
            step_timeouts: !cfg!(target_arch = "wasm32"),
            search: true,
            observation: true,
        }
    }

    pub fn default_module(&self) -> &str {
        self.session.default_module()
    }

    /// Return the compiled rules in the definition selected for execution.
    ///
    /// A written sentence's kind is found by matching its `Source` and `Location` against
    /// `origins`. A position absent from the catalog compiled to no axiom of this definition.
    /// Equal written axioms yield one entry with all their origins. An identity shared by
    /// different entries has `shared_identity = true` and is refused by the observation filter.
    pub fn rule_catalog(
        &self,
        module_name: Option<&str>,
    ) -> Result<Vec<CompiledRuleOutput>, BackendError> {
        let definition = self
            .session
            .definition(module_name)
            .map_err(error("could not select backend module"))?;
        let mut identity_counts = BTreeMap::<&str, usize>::new();
        for axiom in definition.classified_axioms() {
            *identity_counts
                .entry(&axiom.attributes().unique_id)
                .or_default() += 1;
        }
        Ok(definition
            .classified_axioms()
            .iter()
            .map(|axiom| {
                let attributes = axiom.attributes();
                CompiledRuleOutput {
                    id: attributes.unique_id.clone(),
                    kind: match axiom {
                        ClassifiedAxiom::Rewrite { .. } => CompiledRuleKind::Rewrite,
                        ClassifiedAxiom::Function { .. } => CompiledRuleKind::FunctionEquation,
                        ClassifiedAxiom::Simplification { .. } => CompiledRuleKind::Simplification,
                        ClassifiedAxiom::Ceil { .. } => CompiledRuleKind::Definedness,
                    },
                    executable: attributes.executable,
                    label: attributes.label.clone(),
                    priority: attributes.priority,
                    origins: attributes
                        .origins
                        .iter()
                        .map(|origin| CompiledRuleOriginOutput {
                            source: origin.source.clone(),
                            location: origin.location.clone(),
                        })
                        .collect(),
                    shared_identity: identity_counts[attributes.unique_id.as_str()] > 1,
                }
            })
            .collect())
    }

    pub fn select_definition(
        &mut self,
        module: Option<&str>,
    ) -> Result<Arc<BackendDefinition>, SessionError> {
        self.session.definition(module)
    }

    pub fn add_module(&mut self, source: &str, name_as_id: bool) -> Result<String, BackendError> {
        let module = parse_module(source).map_err(error("could not parse KORE module"))?;
        self.add_parsed_module(source, module, name_as_id)
            .map_err(error("could not add KORE module"))
    }

    pub fn add_parsed_module(
        &mut self,
        source: &str,
        module: k_rust_kore::kore::ast::Module,
        name_as_id: bool,
    ) -> Result<String, SessionError> {
        self.session.add_module(source, module, name_as_id)
    }

    /// Execute without observation; every leaf's `branch` and `observations` are empty.
    /// `execute_observed` returns the same non-observation leaf fields in the same order.
    ///
    /// Coverage. The leaves' constraints cover the initial state: take any ground instance of
    /// the initial state that satisfies its constraint. Some leaf's constraint is satisfied by
    /// that instance extended with values for the variables the path introduced. This holds in
    /// both solver profiles under strategy `all`, when no leaf is `depth-bound`,
    /// `breadth-bound`, `branch`, `cut-point`, `timeout` or `cancelled` and no leaf carries
    /// diagnostics.
    /// Every step covers its instances. The applied candidates take the instances where
    /// their result is defined, the remainder takes the instances no rule of the productive
    /// priority group applies to, and a `trivial` leaf takes the instances some rule applies to
    /// without a defined result. That includes the instances where a carried `ensures` or
    /// right-hand-side definedness obligation fails, even when a sibling candidate continues.
    /// A step's `trivial` leaves precede the leaves of its successors.
    /// Strategy `any` makes no coverage claim.
    ///
    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::execute_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn execute(&mut self, request: ExecuteRequest) -> Result<ExecutionResult, BackendError> {
        self.execute_using(request, None)
    }

    /// Execute with observation without changing the leaves or their order.
    /// For the same request, leaves match `execute` after clearing `branch` and `observations`.
    /// Branch identities are independent of the rule filter; `rules: Some(vec![])` returns
    /// every identity and no observation events.
    ///
    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::execute_observed_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn execute_observed(
        &mut self,
        request: ObservedRequest<ExecuteRequest>,
    ) -> Result<ExecutionResult, BackendError> {
        self.execute_using(request.request, Some(request.rules))
    }

    fn execute_using<K: wire::WireKore>(
        &mut self,
        request: ExecuteRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<ExecutionResult<K>, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        #[cfg(target_arch = "wasm32")]
        if request.step_timeout_ms.is_some() || request.moving_average_timeout {
            return Err(BackendError(
                "step timeouts require a host monotonic clock and are unavailable in this WebAssembly build"
                    .into(),
            ));
        }
        let syntax = request.state;
        let module = request.module_name.as_deref();
        self.with_solver_over(module, &[&syntax], |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .admit_unverified(&syntax, &[])
                .internalize_pattern()
                .map_err(error("could not internalize execution state"))?;
            let options = ExecutionOptions {
                max_depth: request.max_depth.unwrap_or(u64::MAX),
                max_breadth: request.max_breadth,
                max_simplification_iterations: request.max_simplification_iterations,
                mode: match request.strategy {
                    ExecutionStrategy::All => ExecutionMode::All,
                    ExecutionStrategy::Any => ExecutionMode::Any,
                },
                branch_mode: if request.stop_at_branch {
                    ExecutionBranchMode::StopAtBranch
                } else {
                    ExecutionBranchMode::ExploreAll
                },
                cut_point_rules: request.cut_point_rules.into_iter().collect(),
                terminal_rules: request.terminal_rules.into_iter().collect(),
                step_timeout: request.step_timeout_ms.map(Duration::from_millis),
                moving_average_timeout: request.moving_average_timeout,
                assume_initial_defined: request.assume_state_defined,
                result_modality: request.result_modality.into(),
                retain_trace: true,
                // The state as received, before its aliases are unfolded: none here, since an
                // executable state has none, but every path names its request the same way.
                request_names: RequestNames::of_received(&[&syntax]),
            };
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    execute_observed_with_solver(definition, initial, options, solver, &observation)
                }
                None => execute_with_solver(definition, initial, options, solver),
            };
            wire::execution_response(result)
        })
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search(&mut self, request: SearchRequest) -> Result<SearchResponse, BackendError> {
        self.search_using(request, None)
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_observed_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search_observed(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<SearchResponse, BackendError> {
        self.search_using(request.request, Some(request.rules))
    }

    fn search_using<K: wire::WireKore>(
        &mut self,
        request: SearchRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<SearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = search_options(&request);
        let syntax = request.state;
        options.request_names = RequestNames::of_received(&[&syntax]);
        let module = request.module_name.as_deref();
        self.with_solver_over(module, &[&syntax], |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .admit_unverified(&syntax, &[])
                .internalize_pattern()
                .map_err(error("could not internalize search state"))?;
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_graph_observed_with_solver(
                        definition,
                        initial,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => search_graph_with_solver(definition, initial, options, solver),
            };
            wire::search_response(result, schema_version)
        })
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_paths_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search_paths(
        &mut self,
        request: SearchRequest,
    ) -> Result<PathSearchResponse, BackendError> {
        self.search_paths_using(request, None)
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_paths_observed_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search_paths_observed(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<PathSearchResponse, BackendError> {
        self.search_paths_using(request.request, Some(request.rules))
    }

    fn search_paths_using<K: wire::WireKore>(
        &mut self,
        request: SearchRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PathSearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = search_options(&request);
        let syntax = request.state;
        options.request_names = RequestNames::of_received(&[&syntax]);
        let module = request.module_name.as_deref();
        self.with_solver_over(module, &[&syntax], |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .admit_unverified(&syntax, &[])
                .internalize_pattern()
                .map_err(error("could not internalize path-search state"))?;
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_paths_observed_with_solver(
                        definition,
                        initial,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => search_paths_with_solver(definition, initial, options, solver),
            };
            wire::path_search_response(result, schema_version)
        })
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_pattern_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search_pattern(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<PatternSearchResponse, BackendError> {
        self.search_pattern_using(request, None)
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_pattern_observed_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search_pattern_observed(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<PatternSearchResponse, BackendError> {
        self.search_pattern_using(request.request, Some(request.rules))
    }

    fn search_pattern_using<K: wire::WireKore>(
        &mut self,
        request: SearchPatternRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PatternSearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = pattern_search_options(&request);
        let initial_syntax = request.state;
        let target_syntax = request.pattern;
        // The target is internalized without the executable check, so it may apply aliases that
        // drop variables the client wrote; the search mints no name spelled like one of them.
        options.request_names = RequestNames::of_received(&[&initial_syntax, &target_syntax]);
        let module = request.module_name.as_deref();
        let patterns = [&initial_syntax, &target_syntax];
        self.with_solver_over(module, &patterns, |definition, solver| {
            definition
                .validate_executable_pattern(&initial_syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .admit_unverified(&initial_syntax, &[])
                .internalize_pattern()
                .map_err(error("could not internalize pattern-search state"))?;
            let target = definition
                .admit_unverified(&target_syntax, &[])
                .internalize_pattern()
                .map_err(error("could not internalize search pattern"))?;
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_pattern_observed_with_solver(
                        definition,
                        initial,
                        &target,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => search_pattern_with_solver(definition, initial, &target, options, solver),
            };
            wire::pattern_search_response(result, schema_version)
        })
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_pattern_paths_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search_pattern_paths(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<PathPatternSearchResponse, BackendError> {
        self.search_pattern_paths_using(request, None)
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::search_pattern_paths_observed_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn search_pattern_paths_observed(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<PathPatternSearchResponse, BackendError> {
        self.search_pattern_paths_using(request.request, Some(request.rules))
    }

    fn search_pattern_paths_using<K: wire::WireKore>(
        &mut self,
        request: SearchPatternRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PathPatternSearchResponse<K>, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let mut options = pattern_search_options(&request);
        let initial_syntax = request.state;
        let target_syntax = request.pattern;
        // The target is internalized without the executable check, so it may apply aliases that
        // drop variables the client wrote; the search mints no name spelled like one of them.
        options.request_names = RequestNames::of_received(&[&initial_syntax, &target_syntax]);
        let module = request.module_name.as_deref();
        let patterns = [&initial_syntax, &target_syntax];
        self.with_solver_over(module, &patterns, |definition, solver| {
            definition
                .validate_executable_pattern(&initial_syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .admit_unverified(&initial_syntax, &[])
                .internalize_pattern()
                .map_err(error("could not internalize path-pattern-search state"))?;
            let target = definition
                .admit_unverified(&target_syntax, &[])
                .internalize_pattern()
                .map_err(error("could not internalize search pattern"))?;
            let result = match observation_rules {
                Some(rules) => {
                    let observation = observation_options(definition, rules)?;
                    search_pattern_paths_observed_with_solver(
                        definition,
                        initial,
                        &target,
                        options,
                        solver,
                        &observation,
                    )
                }
                None => {
                    search_pattern_paths_with_solver(definition, initial, &target, options, solver)
                }
            };
            wire::path_pattern_search_response(result, schema_version)
        })
    }

    /// Write an observed execution response without retaining its expanded KORE JSON as values.
    pub fn execute_observed_to_writer<W: std::io::Write>(
        &mut self,
        request: ObservedRequest<ExecuteRequest>,
        writer: W,
    ) -> Result<(), BackendError> {
        let response = self.execute_using::<Box<RawValue>>(request.request, Some(request.rules))?;
        serde_json::to_writer(writer, &response).map_err(json_output_error)
    }

    pub fn execute_json(&mut self, request: ExecuteRequest) -> Result<String, BackendError> {
        serialize_wire(&self.execute_using::<Box<RawValue>>(request, None)?)
    }

    pub fn execute_observed_json(
        &mut self,
        request: ObservedRequest<ExecuteRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.execute_using::<Box<RawValue>>(request.request, Some(request.rules))?)
    }

    pub fn search_json(&mut self, request: SearchRequest) -> Result<String, BackendError> {
        serialize_wire(&self.search_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_observed_json(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.search_using::<Box<RawValue>>(request.request, Some(request.rules))?)
    }

    pub fn search_paths_json(&mut self, request: SearchRequest) -> Result<String, BackendError> {
        serialize_wire(&self.search_paths_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_paths_observed_json(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(
            &self.search_paths_using::<Box<RawValue>>(request.request, Some(request.rules))?,
        )
    }

    pub fn search_pattern_json(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.search_pattern_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_pattern_observed_json(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(
            &self.search_pattern_using::<Box<RawValue>>(request.request, Some(request.rules))?,
        )
    }

    pub fn search_pattern_paths_json(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<String, BackendError> {
        serialize_wire(&self.search_pattern_paths_using::<Box<RawValue>>(request, None)?)
    }

    pub fn search_pattern_paths_observed_json(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<String, BackendError> {
        serialize_wire(
            &self.search_pattern_paths_using::<Box<RawValue>>(
                request.request,
                Some(request.rules),
            )?,
        )
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::simplify_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn simplify(&mut self, request: PatternRequest) -> Result<Value, BackendError> {
        self.simplify_with(request, |pattern| encode_pattern(&pattern))
    }

    /// [`Self::simplify`] as JSON text, written inside the operation, on the stack it runs on.
    pub fn simplify_json(&mut self, request: PatternRequest) -> Result<String, BackendError> {
        self.simplify_with(request, |pattern| {
            serialize_wire(&encode_pattern(&pattern)?)
        })
    }

    fn simplify_with<T>(
        &mut self,
        request: PatternRequest,
        finish: impl FnOnce(KorePattern) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        let syntax = request.state;
        self.simplify_kore_with(
            request.module_name.as_deref(),
            &syntax,
            Admission::Unverified,
            finish,
        )
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::implies_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn implies(
        &mut self,
        request: ImplicationRequest,
    ) -> Result<ImplicationResult, BackendError> {
        self.implies_with(request, Ok)
    }

    /// [`Self::implies`] as JSON text, written inside the operation, on the stack it runs on.
    pub fn implies_json(&mut self, request: ImplicationRequest) -> Result<String, BackendError> {
        self.implies_with(request, |result| serialize_wire(&result))
    }

    fn implies_with<T>(
        &mut self,
        request: ImplicationRequest,
        finish: impl FnOnce(ImplicationResult) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        let antecedent = request.antecedent;
        let consequent = request.consequent;
        self.implies_kore_with(
            request.module_name.as_deref(),
            &antecedent,
            &consequent,
            Admission::Unverified,
            |verdict, result_sort| {
                finish(ImplicationResult {
                    schema_version: IMPLICATION_SCHEMA_VERSION,
                    status: match verdict.status() {
                        ImplicationStatus::Valid => "valid",
                        ImplicationStatus::Invalid => "invalid",
                        ImplicationStatus::Indeterminate => "unknown",
                    }
                    .into(),
                    failure: verdict.failure().map(|failure| format!("{failure:?}")),
                    condition: verdict
                        .into_condition()
                        .as_ref()
                        .map(|condition| condition_pattern(condition, &result_sort))
                        .transpose()?,
                })
            },
        )
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::get_model_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn get_model(
        &mut self,
        request: PatternRequest,
    ) -> Result<ModelResultOutput, BackendError> {
        self.get_model_with(request, Ok)
    }

    /// [`Self::get_model`] as JSON text, written inside the operation, on the stack it runs on.
    pub fn get_model_json(&mut self, request: PatternRequest) -> Result<String, BackendError> {
        self.get_model_with(request, |result| serialize_wire(&result))
    }

    fn get_model_with<T>(
        &mut self,
        request: PatternRequest,
        finish: impl FnOnce(ModelResultOutput) -> Result<T, BackendError>,
    ) -> Result<T, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        #[cfg(not(feature = "z3-inference"))]
        {
            let _ = (request, finish);
            Err(BackendError(
                "model generation requires an SMT-enabled native build; this WebAssembly build has no Z3".into(),
            ))
        }
        #[cfg(feature = "z3-inference")]
        {
            let syntax = request.state;
            self.model_for_with(
                request.module_name.as_deref(),
                &syntax,
                Admission::Unverified,
                |result, result_sort| {
                    finish(match result {
                        ModelResult::Sat(substitution) => ModelResultOutput {
                            satisfiable: "sat".into(),
                            substitution: result_sort
                                .as_ref()
                                .and_then(|sort| model_substitution(&substitution, sort))
                                .as_ref()
                                .map(encode_pattern)
                                .transpose()?,
                            reason: None,
                        },
                        ModelResult::Unsat => ModelResultOutput {
                            satisfiable: "unsat".into(),
                            substitution: None,
                            reason: None,
                        },
                        ModelResult::Unknown(reason) => ModelResultOutput {
                            satisfiable: "unknown".into(),
                            substitution: None,
                            reason: Some(if result_sort.is_none() {
                                "the pattern contains no model predicate".into()
                            } else {
                                reason
                            }),
                        },
                    })
                },
            )
        }
    }

    /// stack-accepted(facade-value-results): the result's KORE is held as `serde_json::Value`, which its holder drops, clones, formats and serializes one stack frame per level on its own thread; [`Self::prove_json`] writes the same result as text inside the operation. See docs/backend-port.md#stack-bounds.
    pub fn prove(&mut self, request: ProveRequest) -> Result<ProofResultOutput, BackendError> {
        self.prove_using(request)
    }

    /// [`Self::prove`] as JSON text: each leaf's KORE is written as text inside the operation,
    /// on the stack it runs on.
    pub fn prove_json(&mut self, request: ProveRequest) -> Result<String, BackendError> {
        serialize_wire(&self.prove_using::<Box<RawValue>>(request)?)
    }

    fn prove_using<K: wire::WireKore>(
        &mut self,
        request: ProveRequest,
    ) -> Result<ProofResultOutput<K>, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        #[cfg(target_arch = "wasm32")]
        if request.step_timeout_ms.is_some() || request.moving_average_timeout {
            return Err(BackendError(
                "step timeouts require a host monotonic clock and are unavailable in this WebAssembly build"
                    .into(),
            ));
        }
        self.with_solver(request.module_name.as_deref(), |definition, solver| {
            let (claim_index, claim) = proving::select_claim(definition, request.claim.as_deref())?;
            let mut seen = BTreeSet::new();
            let circularities = if let Some(selectors) = &request.circularities {
                let mut circularities = Vec::new();
                for selector in selectors {
                    let (_, candidate) = proving::select_claim(definition, Some(selector))?;
                    if seen.insert(proving::ProvenClaim::from_claim(candidate)) {
                        circularities.push(candidate);
                    }
                }
                circularities
            } else {
                definition
                    .reachability_claims()
                    .iter()
                    .filter(|candidate| {
                        (std::ptr::eq(*candidate, claim) || candidate.attributes.trusted)
                            && seen.insert(proving::ProvenClaim::from_claim(candidate))
                    })
                    .collect()
            };
            let result = proving::run_claim(
                definition,
                claim,
                &circularities,
                ProofOptions {
                    max_depth: request.max_depth.unwrap_or(u64::MAX),
                    min_depth: request.min_depth,
                    breadth_limit: request.breadth_limit,
                    max_counterexamples: request.max_counterexamples,
                    max_simplification_iterations: request.max_simplification_iterations,
                    allow_vacuous: request.allow_vacuous,
                    search_order: if request.depth_first {
                        ProofSearchOrder::DepthFirst
                    } else {
                        ProofSearchOrder::BreadthFirst
                    },
                    stuck_check: request.stuck_check,
                    step_timeout: request.step_timeout_ms.map(Duration::from_millis),
                    moving_average_timeout: request.moving_average_timeout,
                },
                solver,
            )
            .map_err(error("could not prove claim"))?;
            Ok(ProofResultOutput {
                claim: claim
                    .attributes
                    .label
                    .clone()
                    .unwrap_or_else(|| format!("#{claim_index}")),
                status: proof_status(result.status).into(),
                explored_states: result.explored_states,
                unexplored_states: result.unexplored_states,
                leaves: result
                    .leaves
                    .into_iter()
                    .map(|leaf| {
                        Ok(ProofLeafOutput {
                            state: K::from_source(&externalize::constrained_pattern(
                                &leaf.pattern,
                            ))?,
                            depth: leaf.depth,
                            outcome: format!("{:?}", leaf.outcome),
                        })
                    })
                    .collect::<Result<_, BackendError>>()?,
            })
        })
    }

    /// Run `operation` on the definition of `module` with that definition's solver. With the
    /// `z3-inference` feature the run is one operation (`k_rust_backend::stop::operation`): a
    /// request stopped before it starts, or a solver whose prelude already failed, does not run
    /// it, and a prelude failure found while it runs is its result even when `operation`
    /// returned. Such a stop reaches the caller as its [`StopCause`], through `E`'s
    /// `From<StopCause>`.
    ///
    /// The operation runs on a stack that holds the definition's recursive passes over its own
    /// patterns and terms (`BackendDefinition::with_stack_for`); an operation over a request's
    /// patterns uses [`Self::with_solver_over`].
    pub fn with_solver<T, E>(
        &mut self,
        module: Option<&str>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        self.with_solver_over(module, &[], operation)
    }

    /// [`Self::with_solver`] for an operation over the KORE `patterns` of a request.
    ///
    /// The whole operation, from preparing the solver to the result it returns, runs on a stack
    /// that holds the backend's recursive passes over `patterns` with their aliases unfolded,
    /// over the definition, and over the internal terms built from them
    /// (`BackendDefinition::with_stack_for`), so it must return only external results and drop
    /// its internal terms itself. Evaluation that recurses deeper than that stack goes on on
    /// segments up to the operation's simplification stack budget
    /// ([`Self::set_simplification_stack_budget`]). Patterns too deep for the largest stack the
    /// backend provides are refused with `InsufficientStack` before the operation runs.
    pub fn with_solver_over<T, E>(
        &mut self,
        module: Option<&str>,
        patterns: &[&KorePattern],
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        let definition = self
            .session
            .definition(module)
            .map_err(error("could not select backend module"))
            .map_err(E::from)?;
        let depth = definition.operation_depth(patterns);
        let budget = self.simplification_stack_budget;
        k_rust_backend::nesting::with_stack(depth, || {
            k_rust_backend::nesting::with_simplification_stack_budget(budget, || {
                self.run_with_solver(definition, operation)
            })
        })
        .map_err(error("the request is too deep for the backend"))
        .map_err(E::from)?
    }

    #[cfg(feature = "z3-inference")]
    fn run_with_solver<T, E>(
        &mut self,
        definition: Arc<BackendDefinition>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        let module = definition.main_module().to_string();
        if !self.solvers.contains_key(&module) {
            let options = Z3Options {
                timeout_ms: self.options.smt_timeout_ms,
                retry_limit: self.options.smt_retry_limit,
            };
            let solver = if let Some(prelude) = self.smt_prelude.as_deref() {
                Z3Solver::with_options_and_prelude(&definition, options, Some(prelude))
            } else {
                Z3Solver::with_options(&definition, options)
            }
            .map_err(error("could not initialize Z3"))
            .map_err(E::from)?;
            self.solvers.insert(module.clone(), solver);
        }
        let solver = self.solvers.get(&module).expect("solver was inserted");
        // The operation boundary. Its entry poll sees the prelude signal of a solver whose
        // prelude an earlier operation found failed, and a request stopped before it starts, so
        // neither runs; its exit poll sees a prelude failure found during this operation, also
        // one whose stop a refinement dismissed, and that stop replaces `operation`'s value,
        // since no answer of the solver means anything under a failed prelude. The caller
        // receives the cause itself.
        stop::operation(solver, || operation(&definition, solver))
            .map_err(|stop| E::from(stop.into_cause()))?
    }

    #[cfg(not(feature = "z3-inference"))]
    fn run_with_solver<T, E>(
        &mut self,
        definition: Arc<BackendDefinition>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError> + From<StopCause>,
    {
        let _ = self.options;
        operation(&definition, &NoSolver)
    }
}

fn search_options(request: &SearchRequest) -> SearchOptions {
    bounded_search_options(
        request.search_type,
        request.max_depth,
        request.max_breadth,
        request.max_results,
        request.max_simplification_iterations,
    )
}

fn bounded_search_options(
    search_type: SearchTypeArg,
    max_depth: Option<u64>,
    max_breadth: Option<usize>,
    max_results: Option<usize>,
    max_simplification_iterations: usize,
) -> SearchOptions {
    SearchOptions {
        search_type: match search_type {
            SearchTypeArg::Final => SearchType::Final,
            SearchTypeArg::All => SearchType::Star,
            SearchTypeArg::OneStep => SearchType::One,
            SearchTypeArg::OneOrMoreSteps => SearchType::Plus,
        },
        max_depth: max_depth.unwrap_or(u64::MAX),
        max_breadth,
        max_results,
        max_simplification_iterations,
        request_names: RequestNames::default(),
    }
}

fn default_backend_schema_version() -> u32 {
    BACKEND_SCHEMA_VERSION
}

fn default_result_modality() -> ResultModalityOutput {
    ResultModalityOutput::StateSet
}

fn validate_backend_schema_version(schema_version: u32) -> Result<(), BackendError> {
    wire::validate_schema_version(schema_version)
}

fn pattern_search_options(request: &SearchPatternRequest) -> SearchOptions {
    bounded_search_options(
        request.search_type,
        request.max_depth,
        request.max_breadth,
        request.max_results,
        request.max_simplification_iterations,
    )
}

fn observation_options(
    definition: &BackendDefinition,
    rules: Option<Vec<String>>,
) -> Result<ObservationOptions, BackendError> {
    match rules {
        Some(rules) => ObservationOptions::with_rules(definition, rules)
            .map_err(error("could not install observation filter")),
        None => Ok(ObservationOptions::all()),
    }
}

fn encode_pattern(pattern: &KorePattern) -> Result<Value, BackendError> {
    kore_codec::to_value(pattern).map_err(error("could not encode KORE JSON"))
}

fn trace_entry(entry: k_rust_backend::rewrite::TraceEntry) -> TraceEntry {
    TraceEntry {
        depth: entry.depth,
        kind: match entry.kind {
            TraceKind::Simplification => "simplification",
            TraceKind::Rewrite => "rewrite",
            TraceKind::Claim => "claim",
            TraceKind::Remainder => "remainder",
        }
        .into(),
        label: entry.label,
        unique_id: entry.unique_id,
    }
}

/// The published reason of a leaf and its detail: the reason in words, a predicate it names
/// printed at `sort`, the sort of the leaf's term. A consumer branches on the typed reason; the
/// detail is for a reader.
fn halt_reason(
    reason: &HaltReason,
    sort: &Sort,
) -> Result<(HaltReasonOutput, Option<String>), BackendError> {
    let detail = || Some(reason.at(sort).to_string());
    Ok(match reason {
        HaltReason::Stopped(cause) => return stopped_halt_reason(cause),
        HaltReason::Stuck => (HaltReasonOutput::Stuck, None),
        HaltReason::Trivial { .. } => (HaltReasonOutput::Trivial, None),
        HaltReason::Vacuous { .. } => (HaltReasonOutput::Vacuous, None),
        HaltReason::Branch { .. } => (HaltReasonOutput::Branch, detail()),
        HaltReason::CutPointRule { .. } => (HaltReasonOutput::CutPoint, detail()),
        HaltReason::TerminalRule { .. } => (HaltReasonOutput::Terminal, detail()),
        HaltReason::DepthBound => (HaltReasonOutput::DepthBound, None),
        HaltReason::BreadthBound => (HaltReasonOutput::BreadthBound, None),
        HaltReason::Indeterminate(_) => (HaltReasonOutput::Indeterminate, detail()),
        HaltReason::Simplification(error @ SimplificationError::UnsupportedHook { .. }) => {
            (HaltReasonOutput::UnsupportedHook, Some(error.to_string()))
        }
        HaltReason::Simplification(_) => (HaltReasonOutput::SimplificationError, detail()),
    })
}

/// The published reason of a leaf whose state stopped. A cancelled state is `cancelled` and a
/// passed step deadline `timeout`; an exhausted stack keeps the `simplification-error` kind the
/// failure it used to be spelled as had, with the stop as its detail. A failed solver prelude
/// leaves no answer of the operation meaningful, so it is the operation's error, not a leaf.
#[deny(clippy::wildcard_enum_match_arm)]
fn stopped_halt_reason(
    cause: &StopCause,
) -> Result<(HaltReasonOutput, Option<String>), BackendError> {
    match cause {
        StopCause::Cancelled => Ok((HaltReasonOutput::Cancelled, None)),
        StopCause::Deadline(_) => Ok((HaltReasonOutput::Timeout, Some(cause.to_string()))),
        StopCause::StackExhausted(_) => Ok((
            HaltReasonOutput::SimplificationError,
            Some(cause.to_string()),
        )),
        StopCause::SolverPrelude(_) => Err(BackendError::from(cause.clone())),
    }
}

fn condition_pattern(
    condition: &k_rust_backend::implication::ImplicationCondition,
    result_sort: &Sort,
) -> Result<Value, BackendError> {
    let top = || KorePattern::Top {
        sort: externalize::sort(result_sort),
    };
    let predicate = externalize::predicates_pattern(
        &condition.predicates,
        result_sort,
        |predicate| externalize::predicate_pattern(predicate, result_sort),
        externalize::ConjunctionShape::Flat,
    )
    .unwrap_or_else(top);
    let substitution = externalize::substitution_pattern(
        &condition.substitution,
        result_sort,
        externalize::BindingOrder::Container,
        externalize::ConjunctionShape::Flat,
    )
    .unwrap_or_else(top);
    let witnesses = externalize::substitution_pattern(
        &condition.witnesses,
        result_sort,
        externalize::BindingOrder::Container,
        externalize::ConjunctionShape::Flat,
    )
    .unwrap_or_else(top);
    Ok(serde_json::json!({
        "predicate": encode_pattern(&predicate)?,
        "substitution": encode_pattern(&substitution)?,
        "witnesses": encode_pattern(&witnesses)?,
    }))
}

#[cfg(feature = "z3-inference")]
fn model_substitution(substitution: &Substitution, result_sort: &Sort) -> Option<KorePattern> {
    externalize::substitution_pattern(
        substitution,
        result_sort,
        externalize::BindingOrder::Container,
        externalize::ConjunctionShape::Flat,
    )
}

fn proof_status(status: ProofStatus) -> &'static str {
    match status {
        ProofStatus::Proven => "proven",
        ProofStatus::Disproved => "disproved",
        ProofStatus::Failed => "failed",
        ProofStatus::Indeterminate => "indeterminate",
        ProofStatus::DepthBound => "depth-bound",
        ProofStatus::BreadthBound => "breadth-bound",
    }
}

/// Admit `pattern`, read from outside the definition, to internalization under `sort_variables`
/// as `admission` decides. A `Verified` admission runs the standalone verifier under the same
/// sort variables the witness carries to internalization, and reports its failure with the
/// verifier's message, naming the input as `what`.
fn admit<'a>(
    definition: &'a BackendDefinition,
    pattern: &'a KorePattern,
    sort_variables: &'a [Name],
    admission: Admission,
    what: &str,
) -> Result<Admitted<'a>, BackendError> {
    match admission {
        Admission::Verified => definition
            .verify_standalone_pattern(pattern, sort_variables)
            .map_err(|cause| BackendError(format!("invalid {what}: {cause}"))),
        Admission::Unverified => Ok(definition.admit_unverified(pattern, sort_variables)),
    }
}

fn error<E: fmt::Display>(context: &'static str) -> impl FnOnce(E) -> BackendError {
    move |cause| BackendError(format!("{context}: {cause}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::{parser::parse_pattern, printer::Printer};
    use std::collections::BTreeSet;

    #[test]
    fn execution_halt_reasons_match_typescript_declarations() {
        let expected: BTreeSet<String> = HaltReasonOutput::ALL
            .into_iter()
            .map(|reason| {
                let spelling = serde_json::to_string(&reason).unwrap();
                assert_eq!(
                    serde_json::from_str::<HaltReasonOutput>(&spelling).unwrap(),
                    reason
                );
                serde_json::from_str::<String>(&spelling).unwrap()
            })
            .collect();
        assert_eq!(expected.len(), HaltReasonOutput::ALL.len());

        for package in ["k-rust-napi", "k-rust-wasm"] {
            let path = format!(
                "{}/../{package}/typescript/index.ts",
                env!("CARGO_MANIFEST_DIR")
            );
            let declaration = std::fs::read_to_string(&path).unwrap();
            let leaf = declaration
                .split_once("export interface ExecutionLeaf {")
                .unwrap()
                .1;
            let union = leaf.split_once("  reason:\n").unwrap().1;
            let actual: BTreeSet<String> = union
                .lines()
                .take_while(|line| line.trim_start().starts_with('|'))
                .map(|line| {
                    line.trim()
                        .trim_start_matches('|')
                        .trim()
                        .trim_matches('\'')
                        .to_string()
                })
                .collect();
            assert_eq!(actual, expected, "{path}");
        }
    }

    const DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            sort SortT{} []
            symbol a{}() : SortS{} [constructor{}()]
            symbol b{}() : SortS{} [constructor{}()]
            symbol c{}() : SortS{} [constructor{}()]
            symbol t{}() : SortT{} [constructor{}()]
            symbol macroValue{}() : SortS{} [constructor{}(), macro{}()]
            alias weakExistsFinally{S}(S) : S
                where weakExistsFinally{S}(@X:S) := @X:S []
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(a{}(), \top{SortS{}}()),
                \and{SortS{}}(b{}(), \top{SortS{}}())
            ) [label{}("a-to-b")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(b{}(), \top{SortS{}}()),
                \and{SortS{}}(c{}(), \top{SortS{}}())
            ) [label{}("b-to-c")]
            claim{} \implies{SortS{}}(
                \and{SortS{}}(\top{SortS{}}(), a{}()),
                weakExistsFinally{SortS{}}(
                    \and{SortS{}}(c{}(), \top{SortS{}}())
                )
            ) [label{}("reaches-c")]
        endmodule []"#;

    const DIAMOND_DEFINITION: &str = r#"[]
        module DIAMOND
            sort SortS{} []
            symbol initial{}() : SortS{} [constructor{}()]
            symbol left{}() : SortS{} [constructor{}()]
            symbol right{}() : SortS{} [constructor{}()]
            symbol merged{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(initial{}(), \top{SortS{}}()), left{}()
            ) [label{}("initial-left")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(initial{}(), \top{SortS{}}()), right{}()
            ) [label{}("initial-right")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(left{}(), \top{SortS{}}()), merged{}()
            ) [label{}("left-merged")]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(right{}(), \top{SortS{}}()), merged{}()
            ) [label{}("right-merged")]
        endmodule []"#;

    const LOG_DEFINITION: &str = r#"[]
        module MAIN
            sort SortString{} [hasDomainValues{}()]
            sort SortK{} []
            symbol dotk{}() : SortK{} [constructor{}()]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), total{}(), hook{}("IO.logString")]
        endmodule []"#;

    const EFFECTFUL_BRANCH_DEFINITION: &str = r#"[]
        module MAIN
            sort SortString{} [hasDomainValues{}()]
            sort SortK{} []
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol left{}(SortK{}) : SortState{} [constructor{}()]
            symbol right{}(SortK{}) : SortState{} [constructor{}()]
            symbol dotk{}() : SortK{} [constructor{}()]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), hook{}("IO.logString")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                left{}(log{}(\dv{SortString{}}("left")))
            ) [label{}("left")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                right{}(log{}(\dv{SortString{}}("right")))
            ) [label{}("right")]
        endmodule []"#;

    const OBSERVATION_ERASURE_DEFINITION: &str = r#"[]
        module MAIN
            sort SortString{} [hasDomainValues{}()]
            sort SortK{} []
            sort SortState{} []
            symbol initial{}() : SortState{} [constructor{}()]
            symbol left{}(SortK{}) : SortState{} [constructor{}()]
            symbol right{}(SortK{}) : SortState{} [constructor{}()]
            symbol merged{}() : SortState{} [constructor{}()]
            symbol dotk{}() : SortK{} [constructor{}()]
            hooked-symbol log{}(SortString{}) : SortK{}
                [function{}(), hook{}("IO.logString")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                left{}(log{}(\dv{SortString{}}("same")))
            ) [label{}("left")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(initial{}(), \top{SortState{}}()),
                right{}(log{}(\dv{SortString{}}("same")))
            ) [label{}("right")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(left{}(dotk{}()), \top{SortState{}}()), merged{}()
            ) [label{}("left-merged")]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(right{}(dotk{}()), \top{SortState{}}()), merged{}()
            ) [label{}("right-merged")]
        endmodule []"#;

    const UNSUPPORTED_HOOK_DEFINITION: &str = r#"[]
        module MAIN
            sort SortState{} [hasDomainValues{}()]
            hooked-symbol missing{}(SortState{}) : SortState{}
                [function{}(), hook{}("TEST.missing")]
        endmodule []"#;

    #[cfg(not(feature = "z3-inference"))]
    const INDETERMINATE_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            symbol wrap{}(SortInt{}) : SortS{} [constructor{}()]
            symbol done{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(
                    wrap{}(X:SortInt{}),
                    \equals{SortInt{}, SortS{}}(X:SortInt{}, \dv{SortInt{}}("0"))
                ), done{}()
            ) [label{}("guarded")]
        endmodule []"#;

    #[cfg(not(feature = "z3-inference"))]
    const NARROWING_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
            symbol zero{}() : SortS{} [constructor{}()]
            symbol done{}() : SortS{} [constructor{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(zero{}()), \top{SortS{}}()), done{}()
            ) [label{}("narrow")]
        endmodule []"#;

    #[cfg(not(feature = "z3-inference"))]
    const SET_BINDING_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
            symbol pair{}(SortS{}, SortS{}) : SortS{}
                [function{}(), total{}(), injective{}(), no-evaluators{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(wrap{}(I:SortS{}), \top{SortS{}}()),
                pair{}(I:SortS{}, I:SortS{})
            ) [label{}("duplicate")]
        endmodule []"#;

    #[cfg(not(feature = "z3-inference"))]
    #[test]
    fn execution_indeterminate_leaves_publish_search_causes() {
        let cases = [
            (INDETERMINATE_DEFINITION, "wrap{}(Y:SortInt{})", "requires"),
            (NARROWING_DEFINITION, "wrap{}(Y:SortS{})", "smt"),
            (SET_BINDING_DEFINITION, "wrap{}(@Y:SortS{})", "match"),
        ];
        for (definition, state, kind) in cases {
            let mut backend = Backend::new(definition, "MAIN", BackendOptions::default()).unwrap();
            let leaf = backend
                .execute(ExecuteRequest::new(kore(state)))
                .unwrap()
                .leaves
                .remove(0);
            assert_eq!(leaf.reason, HaltReasonOutput::Indeterminate, "{state}");
            let encoded = serde_json::to_value(&leaf).unwrap();
            assert_eq!(encoded["cause"]["kind"], kind, "{state}: {encoded}");
            assert!(encoded["cause"]["rule"].is_string(), "{encoded}");
            assert_eq!(
                leaf.cause.as_ref().unwrap().solver_unavailable(),
                kind != "match"
            );
            if kind == "smt" {
                assert_eq!(encoded["cause"]["error"]["kind"], "unavailable");
            }
            let decoded: ExecutionLeaf = serde_json::from_value(encoded.clone()).unwrap();
            assert_eq!(serde_json::to_value(decoded).unwrap(), encoded);
        }
        let leaf = backend()
            .execute(ExecuteRequest::new(kore("a{}()")))
            .unwrap()
            .leaves
            .remove(0);
        assert_ne!(leaf.reason, HaltReasonOutput::Indeterminate);
        assert!(leaf.cause.is_none());
        assert!(serde_json::to_value(leaf).unwrap().get("cause").is_none());
    }

    fn backend() -> Backend {
        Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap()
    }

    /// A request the backend refuses is refused in words that name what is wrong: the rule
    /// filter's unknown id, the sort an added module may not declare, what an execution state
    /// lacks or has that a constrained term may not (without saying it is a rule's), the token a
    /// module's text may not have.
    #[test]
    fn refused_requests_are_stated_in_words() {
        let mut backend = backend();
        let filter = backend
            .execute_observed(ObservedRequest {
                request: ExecuteRequest::new(kore("a{}()")),
                rules: Some(vec!["missing".into()]),
            })
            .unwrap_err();
        assert_eq!(
            filter.0,
            "could not install observation filter: no executable rewrite, function equation, \
             simplification or definedness rule has the id 'missing'"
        );
        let sorted = backend
            .add_module(
                "module NEWSORT import MAIN [] sort SortNew{} [] endmodule []",
                false,
            )
            .unwrap_err();
        assert_eq!(
            sorted.0,
            "could not add KORE module: an added module may not declare sorts, and this one \
             declares 'SortNew'"
        );
        let predicate = backend
            .execute(ExecuteRequest::new(kore(r"\top{SortS{}}()")))
            .unwrap_err();
        assert_eq!(
            predicate.0,
            "could not internalize execution state: Invalid pattern: the pattern states no term, \
             only predicates, where a term is needed"
        );
        let disjunction = backend
            .execute(ExecuteRequest::new(kore(r"\or{SortS{}}(a{}(), b{}())")))
            .unwrap_err();
        assert_eq!(
            disjunction.0,
            "could not internalize execution state: Invalid pattern: a term of the pattern is a \
             disjunction (\\or) of terms where one term is needed"
        );
        let rewrite = r"\and{SortS{}}(a{}(), \rewrites{SortS{}}(a{}(), b{}()))";
        let rewrite = backend
            .execute(ExecuteRequest::new(kore(rewrite)))
            .unwrap_err();
        assert_eq!(
            rewrite.0,
            "could not internalize execution state: Invalid pattern: a predicate of the pattern \
             uses \\rewrites, which the backend does not read as a predicate"
        );
        let trailing = "module BROKEN import MAIN [] endmodule [] ]";
        let broken = backend.add_module(trailing, false).unwrap_err();
        assert_eq!(
            broken.0,
            format!(
                "could not parse KORE module: unexpected trailing token ']' at byte {}",
                trailing.len() - 1
            )
        );
    }

    #[test]
    fn json_text_paths_match_value_responses() {
        let execute = || ExecuteRequest::new(kore("a{}()"));
        let search = || SearchRequest::new(kore("a{}()"));
        let pattern = || SearchPatternRequest::new(kore("a{}()"), kore("c{}()"));
        let observed_execute = || ObservedRequest {
            request: execute(),
            rules: None,
        };
        let observed_search = || ObservedRequest {
            request: search(),
            rules: None,
        };
        let observed_pattern = || ObservedRequest {
            request: pattern(),
            rules: None,
        };

        macro_rules! same_json {
            ($value_method:ident, $json_method:ident, $request:expr) => {{
                let expected =
                    serde_json::to_string(&backend().$value_method($request).unwrap()).unwrap();
                let actual = backend().$json_method($request).unwrap();
                assert_eq!(actual, expected, stringify!($json_method));
            }};
        }
        same_json!(execute, execute_json, execute());
        same_json!(execute_observed, execute_observed_json, observed_execute());
        same_json!(search, search_json, search());
        same_json!(search_observed, search_observed_json, observed_search());
        same_json!(search_paths, search_paths_json, search());
        same_json!(
            search_paths_observed,
            search_paths_observed_json,
            observed_search()
        );
        same_json!(search_pattern, search_pattern_json, pattern());
        same_json!(
            search_pattern_observed,
            search_pattern_observed_json,
            observed_pattern()
        );
        same_json!(search_pattern_paths, search_pattern_paths_json, pattern());
        same_json!(
            search_pattern_paths_observed,
            search_pattern_paths_observed_json,
            observed_pattern()
        );

        let mut written = Vec::new();
        backend()
            .execute_observed_to_writer(observed_execute(), &mut written)
            .unwrap();
        assert_eq!(
            written,
            backend()
                .execute_observed_json(observed_execute())
                .unwrap()
                .into_bytes()
        );
    }

    #[test]
    fn executable_facade_rejects_nested_macro_and_alias_states_before_internalization() {
        let alias = kore("weakExistsFinally{SortS{}}(a{}())");
        let nested_macro = kore(r#"\and{SortS{}}(a{}(), macroValue{}())"#);
        let assert_invalid = |error: BackendError, symbol: &str| {
            let error = error.to_string();
            assert!(error.contains("invalid executable state"), "{error}");
            assert!(error.contains(symbol), "{error}");
        };

        assert_invalid(
            backend()
                .execute(ExecuteRequest::new(alias.clone()))
                .unwrap_err(),
            "weakExistsFinally",
        );
        assert_invalid(
            backend()
                .search(SearchRequest::new(nested_macro.clone()))
                .unwrap_err(),
            "macroValue",
        );
        assert_invalid(
            backend()
                .search_paths(SearchRequest::new(alias.clone()))
                .unwrap_err(),
            "weakExistsFinally",
        );
        assert_invalid(
            backend()
                .search_pattern(SearchPatternRequest::new(nested_macro, kore("a{}()")))
                .unwrap_err(),
            "macroValue",
        );
        assert_invalid(
            backend()
                .search_pattern_paths(SearchPatternRequest::new(alias, kore("a{}()")))
                .unwrap_err(),
            "weakExistsFinally",
        );
    }

    fn kore(source: &str) -> KorePattern {
        parse_pattern(source).unwrap()
    }

    fn json(source: &str) -> Value {
        encode_pattern(&kore(source)).unwrap()
    }

    fn text(value: Value) -> String {
        Printer::compact().print_pattern(&kore_codec::from_value(&value).unwrap())
    }

    #[test]
    fn search_wire_types_round_trip_every_disposition() {
        let state = SearchStateOutput {
            state: json("a{}()"),
            diagnostics: vec![BackendDiagnosticOutput::SimplificationBudgetExhausted {
                limit: 3,
                subject: BudgetSubjectOutput::Term,
            }],
            depth: 1,
            trace: Vec::new(),
            branch: Vec::new(),
            observations: Vec::new(),
        };
        let variants = vec![
            IncompleteSearchOutput::ResultBound,
            IncompleteSearchOutput::DepthBound {
                state: state.clone(),
            },
            IncompleteSearchOutput::BreadthBound {
                states: vec![state.clone()],
            },
            IncompleteSearchOutput::Indeterminate {
                state: state.clone(),
                reason: SearchFailureOutput::Requires {
                    rule: "rule-id".into(),
                    predicates: Vec::new(),
                },
            },
            IncompleteSearchOutput::Cancelled {
                state: state.clone(),
            },
            IncompleteSearchOutput::Simplification {
                state: state.clone(),
                error: SearchFailureOutput::IterationLimit {
                    limit: 100,
                    term: None,
                },
            },
            IncompleteSearchOutput::Match {
                state: state.clone(),
                bindings: Vec::new(),
                remainder: Vec::new(),
            },
            IncompleteSearchOutput::Smt {
                state,
                error: SmtFailureOutput::Unavailable,
            },
        ];

        for expected in variants {
            let json = serde_json::to_string(&expected).unwrap();
            let actual = serde_json::from_str::<IncompleteSearchOutput>(&json).unwrap();
            assert_eq!(actual, expected, "{json}");
        }

        let effect = EffectOutput::UserLog {
            message: "hello".into(),
        };
        let json = serde_json::to_string(&effect).unwrap();
        assert_eq!(serde_json::from_str::<EffectOutput>(&json).unwrap(), effect);
        assert!(serde_json::from_str::<EffectOutput>(r#"{"kind":"future"}"#).is_err());
        assert!(
            serde_json::from_str::<EffectOutput>(
                r#"{"kind":"user-log","message":"hello","future":true}"#,
            )
            .is_err()
        );
    }

    #[test]
    fn search_request_rejects_unknown_fields_and_schemas() {
        assert!(serde_json::from_str::<SearchRequest>(r#"{"bogus":1}"#).is_err());

        let request = serde_json::from_value::<SearchRequest>(serde_json::json!({
            "state": json("a{}()"),
            "schemaVersion": 99,
        }))
        .unwrap();
        let error = request.validate_schema().unwrap_err();
        assert!(error.to_string().contains("schema version 99"), "{error}");
        assert!(error.to_string().contains("version 1"), "{error}");
    }

    #[test]
    fn legacy_persistent_requests_reject_unknown_fields() {
        assert!(serde_json::from_str::<BackendOptions>(r#"{"bogus":1}"#).is_err());
        assert!(serde_json::from_str::<ExecuteRequest>(r#"{"state":null,"bogus":1}"#).is_err());
        assert!(serde_json::from_str::<PatternRequest>(r#"{"state":null,"bogus":1}"#).is_err());
        assert!(
            serde_json::from_str::<ImplicationRequest>(
                r#"{"antecedent":null,"consequent":null,"bogus":1}"#,
            )
            .is_err()
        );
        assert!(serde_json::from_str::<ProveRequest>(r#"{"bogus":1}"#).is_err());

        let error = backend()
            .execute(ExecuteRequest {
                schema_version: 99,
                ..ExecuteRequest::new(kore("a{}()"))
            })
            .unwrap_err();
        assert!(error.to_string().contains("schema version 99"), "{error}");
    }

    const DEEP_REQUEST_LEVELS: usize = 200_000;

    /// KORE JSON for a `\not` chain `levels` deep, built without a JSON value.
    fn deep_kore_json(levels: usize) -> String {
        let sort = r#"{"tag":"SortApp","name":"SortK","args":[]}"#;
        let mut json = String::from(r#"{"format":"KORE","version":1,"term":"#);
        for _ in 0..levels {
            json.push_str(&format!(r#"{{"tag":"Not","sort":{sort},"arg":"#));
        }
        json.push_str(&format!(r#"{{"tag":"Top","sort":{sort}}}"#));
        json.push_str(&"}".repeat(levels + 1));
        json
    }

    fn deep_not_depth(mut pattern: &KorePattern) -> usize {
        let mut depth = 0;
        while let KorePattern::Not { argument, .. } = pattern {
            depth += 1;
            pattern = argument;
        }
        depth
    }

    #[test]
    fn deep_kore_request_fields_decode_on_the_test_thread() {
        let deep = deep_kore_json(DEEP_REQUEST_LEVELS);

        let execute =
            deserialize_request::<ExecuteRequest>(&format!(r#"{{"state":{deep},"maxDepth":0}}"#))
                .unwrap();
        assert_eq!(deep_not_depth(&execute.state), DEEP_REQUEST_LEVELS);
        assert_eq!(execute.max_depth, Some(0));
        drop(execute);

        let observed = deserialize_request::<ObservedRequest<SearchPatternRequest>>(&format!(
            r#"{{"request":{{"state":{deep},"pattern":{deep}}},"rules":[]}}"#
        ))
        .unwrap();
        assert_eq!(deep_not_depth(&observed.request.state), DEEP_REQUEST_LEVELS);
        assert_eq!(observed.request.state, observed.request.pattern);
        drop(observed);

        let implication = deserialize_request::<ImplicationRequest>(&format!(
            r#"{{"antecedent":{deep},"consequent":{deep}}}"#
        ))
        .unwrap();
        assert_eq!(deep_not_depth(&implication.consequent), DEEP_REQUEST_LEVELS);
        drop(implication);

        let simplify =
            deserialize_request::<PatternRequest>(&format!(r#"{{"state":{deep}}}"#)).unwrap();
        assert_eq!(
            format!("{simplify:?}").matches("Not {").count(),
            DEEP_REQUEST_LEVELS
        );
    }

    #[test]
    fn deep_malformed_kore_request_fields_are_ordinary_errors() {
        let unclosed_arrays = format!(r#"{{"state":{}"#, "[".repeat(DEEP_REQUEST_LEVELS));
        let error = deserialize_request::<ExecuteRequest>(&unclosed_arrays).unwrap_err();
        assert!(error.to_string().contains("EOF"), "{error}");

        let deep = deep_kore_json(DEEP_REQUEST_LEVELS);
        let unclosed_term = format!(r#"{{"state":{}"#, &deep[..deep.len() - 10]);
        let error = deserialize_request::<SearchRequest>(&unclosed_term).unwrap_err();
        assert!(error.to_string().contains("EOF"), "{error}");

        let mut wrong_tag = deep.replacen(r#""tag":"Top""#, r#""tag":"Bogus""#, 1);
        let error = deserialize_request::<SearchRequest>(&format!(r#"{{"state":{wrong_tag}}}"#))
            .unwrap_err();
        assert!(error.to_string().contains("invalid KORE JSON"), "{error}");
        wrong_tag.clear();

        let error = deserialize_request::<ExecuteRequest>(r#"{"maxDepth":0}"#).unwrap_err();
        assert!(
            error.to_string().contains("missing field `state`"),
            "{error}"
        );
        let error = deserialize_request::<ExecuteRequest>(r#"{"state":null}"#).unwrap_err();
        assert!(error.to_string().contains("invalid KORE JSON"), "{error}");
    }

    /// No field outside the KORE fields has a type that nests, so serde rejects a deep value
    /// there at its first level, with its recursion limit as a backstop.
    #[test]
    fn deep_values_outside_kore_fields_are_ordinary_errors() {
        let state = deep_kore_json(1);
        let nested = format!(
            "{}{}",
            "[".repeat(DEEP_REQUEST_LEVELS),
            "]".repeat(DEEP_REQUEST_LEVELS)
        );
        for request in [
            format!(r#"{{"state":{state},"moduleName":{nested}}}"#),
            format!(r#"{{"state":{state},"cutPointRules":{nested}}}"#),
            format!(r#"{{"state":{state},"bogus":{nested}}}"#),
        ] {
            assert!(deserialize_request::<ExecuteRequest>(&request).is_err());
        }
        assert!(
            deserialize_request::<ObservedRequest<ExecuteRequest>>(&format!(
                r#"{{"request":{{"state":{state}}},"rules":{nested}}}"#
            ))
            .is_err()
        );
    }

    #[test]
    fn prove_request_accepts_explicit_circularities() {
        assert!(
            serde_json::from_str::<ProveRequest>(
                r#"{"claim":"reaches-c","circularities":["reaches-c"]}"#,
            )
            .is_ok()
        );
    }

    #[test]
    fn persistent_proof_uses_only_explicit_or_trusted_circularities() {
        let definition = r#"[]
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                symbol d{}() : SortS{} [constructor{}()]
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()), b{}()
                ) [label{}("a-to-b")]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}()), c{}()
                ) [label{}("b-to-c")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(d{}())
                ) [label{}("ca")]
                claim{} \implies{SortS{}}(
                    \and{SortS{}}(b{}(), \top{SortS{}}()),
                    weakAlwaysFinally{SortS{}}(d{}())
                ) [label{}("cb"), trusted{}()]
            endmodule []"#;

        let mut backend = Backend::new(definition, "MAIN", BackendOptions::default()).unwrap();
        let default = backend
            .prove(ProveRequest {
                claim: Some("ca".into()),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(default.status, "proven");

        let isolated = backend
            .prove(ProveRequest {
                claim: Some("ca".into()),
                circularities: Some(vec!["ca".into()]),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(isolated.status, "disproved");
    }

    #[test]
    fn persistent_proof_keeps_both_modalities_under_one_emitted_id() {
        let definition = r#"[]
            module MAIN
                sort SortS{} []
                symbol a{}() : SortS{} [constructor{}()]
                symbol b{}() : SortS{} [constructor{}()]
                symbol c{}() : SortS{} [constructor{}()]
                alias weakExistsFinally{S}(S) : S
                    where weakExistsFinally{S}(@X:S) := @X:S []
                alias weakAlwaysFinally{S}(S) : S
                    where weakAlwaysFinally{S}(@X:S) := @X:S []
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(a{}(), \top{SortS{}}()), b{}()
                ) []
                claim{} \implies{SortS{}}(a{}(), weakAlwaysFinally{SortS{}}(c{}()))
                    [label{}("goal")]
                claim{} \implies{SortS{}}(b{}(), weakExistsFinally{SortS{}}(c{}()))
                    [label{}("one"), trusted{}(), UNIQUE'Unds'ID{}("shared")]
                claim{} \implies{SortS{}}(b{}(), weakAlwaysFinally{SortS{}}(c{}()))
                    [label{}("all"), trusted{}(), UNIQUE'Unds'ID{}("shared")]
            endmodule []"#;
        let mut backend = Backend::new(definition, "MAIN", BackendOptions::default()).unwrap();
        let result = backend
            .prove(ProveRequest {
                claim: Some("goal".into()),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(result.status, "proven");
    }

    #[test]
    fn encodes_deep_patterns_without_the_default_json_recursion_limit() {
        let mut source = r"\top{SortS{}}()".to_owned();
        for _ in 0..160 {
            source = format!(r"\not{{SortS{{}}}}({source})");
        }

        let pattern = parse_pattern(&source).unwrap();
        assert!(encode_pattern(&pattern).is_ok());
    }

    #[test]
    fn persistent_backend_executes_and_proves() {
        let mut backend = backend();
        let execution = backend
            .execute(ExecuteRequest {
                max_depth: Some(2),
                ..ExecuteRequest::new(kore("a{}()"))
            })
            .unwrap();
        assert_eq!(execution.leaves.len(), 1);
        assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        assert!(
            serde_json::to_value(&execution).unwrap()["leaves"][0]
                .get("diagnostics")
                .is_none()
        );

        let implication = backend
            .implies(ImplicationRequest {
                antecedent: kore("X:S"),
                consequent: kore("X:S"),
                module_name: None,
                schema_version: BACKEND_SCHEMA_VERSION,
            })
            .unwrap();
        assert_eq!(implication.status, "valid");

        let proof = backend
            .prove(ProveRequest {
                claim: Some("reaches-c".into()),
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(proof.status, "proven");
    }

    #[test]
    fn execution_exposes_the_leaf_budget_diagnostic_on_the_wire() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-budget.kore"),
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();
        let result = backend
            .execute(ExecuteRequest {
                max_simplification_iterations: 3,
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        assert_eq!(result.leaves.len(), 1);
        let value = serde_json::to_value(result).unwrap();
        assert_eq!(
            value["leaves"][0]["diagnostics"],
            serde_json::json!([{
                "kind": "simplification-budget-exhausted",
                "limit": 3,
                "subject": "term"
            }])
        );
    }

    /// A leaf's `detail` is for a reader: a branch states its successors' count and rules in
    /// words, not the reason's Rust value with its patterns and substitutions.
    #[test]
    fn a_branch_leaf_states_its_detail_in_words() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-candidates.kore"),
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();
        let result = backend
            .execute(ExecuteRequest {
                stop_at_branch: true,
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        let [leaf] = result.leaves.as_slice() else {
            panic!("expected one branch leaf: {:?}", result.leaves);
        };
        assert_eq!(leaf.reason, HaltReasonOutput::Branch);
        let detail = leaf.detail.as_deref().unwrap_or_default();
        assert!(
            ["to-b and to-g", "to-g and to-b"]
                .map(|rules| format!("the step branches into 2 successors by rules {rules}"))
                .contains(&detail.to_owned()),
            "{detail}"
        );
    }

    #[test]
    fn branch_candidates_expose_only_their_own_diagnostics_on_the_wire() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-candidates.kore"),
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();
        let result = backend
            .execute(ExecuteRequest {
                max_simplification_iterations: 3,
                stop_at_branch: true,
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        let value = serde_json::to_value(result).unwrap();
        let [leaf] = value["leaves"].as_array().unwrap().as_slice() else {
            panic!("expected one branch leaf: {value}");
        };
        assert_eq!(leaf["reason"], "branch");
        assert!(leaf.get("diagnostics").is_none());
        let candidates = leaf["candidates"].as_array().unwrap();
        assert_eq!(candidates.len(), 2);
        let diagnosed = candidates
            .iter()
            .find(|candidate| candidate["label"] == "to-g")
            .unwrap();
        assert_eq!(
            diagnosed["diagnostics"],
            serde_json::json!([{
                "kind": "simplification-budget-exhausted",
                "limit": 3,
                "subject": "term"
            }])
        );
        let plain = candidates
            .iter()
            .find(|candidate| candidate["label"] == "to-b")
            .unwrap();
        assert!(plain.get("diagnostics").is_none());
        assert_eq!(text(plain["state"].clone()), "b{}()");
    }

    #[test]
    fn cut_point_candidates_expose_their_diagnostics_on_the_wire() {
        let mut backend = Backend::new(
            include_str!("../../tests/fixtures/execution-budget.kore"),
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();
        let result = backend
            .execute(ExecuteRequest {
                max_simplification_iterations: 3,
                cut_point_rules: vec!["to-g".into()],
                ..ExecuteRequest::new(kore("start{}()"))
            })
            .unwrap();
        let value = serde_json::to_value(result).unwrap();
        let [leaf] = value["leaves"].as_array().unwrap().as_slice() else {
            panic!("expected one cut-point leaf: {value}");
        };
        assert_eq!(leaf["reason"], "cut-point");
        assert!(leaf.get("diagnostics").is_none());
        assert_eq!(leaf["candidates"].as_array().unwrap().len(), 1);
        assert_eq!(leaf["candidates"][0]["label"], "to-g");
        assert_eq!(
            leaf["candidates"][0]["diagnostics"],
            serde_json::json!([{
                "kind": "simplification-budget-exhausted",
                "limit": 3,
                "subject": "term"
            }])
        );
    }

    fn search_diagnostics_backend() -> Backend {
        Backend::new(
            include_str!("../../tests/fixtures/search-diagnostics.kore"),
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap()
    }

    fn term_exhausted_json() -> Value {
        serde_json::json!([{
            "kind": "simplification-budget-exhausted",
            "limit": 3,
            "subject": "term"
        }])
    }

    fn condition_exhausted_json(rule_id: &str) -> Value {
        serde_json::json!([
            {"kind": "simplification-budget-exhausted", "limit": 3, "subject": "predicates"},
            {"kind": "rule-condition-unsimplified", "ruleId": rule_id, "limit": 3}
        ])
    }

    /// The entry of `entries` whose `field` state prints starting with `state`.
    fn entry_at<'a>(entries: &'a Value, field: Option<&str>, state: &str) -> &'a Value {
        entries
            .as_array()
            .unwrap()
            .iter()
            .find(|entry| {
                let entry = field.map_or(*entry, |field| &entry[field]);
                text(entry["state"].clone()).starts_with(state)
            })
            .unwrap_or_else(|| panic!("no entry at {state}: {entries:#}"))
    }

    #[test]
    fn search_states_and_witnesses_expose_their_paths_diagnostics_on_the_wire() {
        let mut backend = search_diagnostics_backend();
        let request = SearchRequest {
            max_simplification_iterations: 3,
            ..SearchRequest::new(kore("start{}()"))
        };

        let states = serde_json::to_value(backend.search(request.clone()).unwrap()).unwrap();
        let paths = serde_json::to_value(backend.search_paths(request).unwrap()).unwrap();

        assert_eq!(states["states"].as_array().unwrap().len(), 3, "{states:#}");
        assert_eq!(states["incomplete"], serde_json::json!([]));
        assert_eq!(
            entry_at(&states["states"], None, "held{}(")["diagnostics"],
            term_exhausted_json()
        );
        assert!(
            entry_at(&states["states"], None, "b{}()")
                .get("diagnostics")
                .is_none()
        );
        assert_eq!(
            entry_at(&states["states"], None, "c{}()")["diagnostics"],
            condition_exhausted_json("norm-c")
        );
        assert_eq!(paths["witnesses"].as_array().unwrap().len(), 3, "{paths:#}");
        assert_eq!(
            entry_at(&paths["witnesses"], None, "held{}(")["diagnostics"],
            term_exhausted_json()
        );
        assert!(
            entry_at(&paths["witnesses"], None, "b{}()")
                .get("diagnostics")
                .is_none()
        );
        assert_eq!(
            entry_at(&paths["witnesses"], None, "c{}()")["diagnostics"],
            condition_exhausted_json("norm-c")
        );
    }

    #[test]
    fn search_matches_expose_their_own_diagnostics_apart_from_their_states_on_the_wire() {
        let mut backend = search_diagnostics_backend();
        let request = SearchPatternRequest {
            max_simplification_iterations: 3,
            ..SearchPatternRequest::new(
                kore("start{}()"),
                kore(
                    r#"\and{SortS{}}(X:SortS{}, \equals{SortS{}, SortS{}}(check{}(X:SortS{}), ok{}()))"#,
                ),
            )
        };

        let states =
            serde_json::to_value(backend.search_pattern(request.clone()).unwrap()).unwrap();
        let paths = serde_json::to_value(backend.search_pattern_paths(request).unwrap()).unwrap();

        for (response, field) in [(&states, "state"), (&paths, "witness")] {
            let on_b = entry_at(&response["matches"], Some(field), "b{}()");
            assert!(on_b[field].get("diagnostics").is_none(), "{response:#}");
            assert_eq!(on_b["diagnostics"], condition_exhausted_json("check-ok"));
            let on_c = entry_at(&response["matches"], Some(field), "c{}()");
            assert_eq!(
                on_c[field]["diagnostics"],
                condition_exhausted_json("norm-c")
            );
            assert_eq!(on_c["diagnostics"], condition_exhausted_json("check-ok"));
        }
    }

    #[test]
    fn persistent_backend_answers_implications_between_bottom_top_and_a_regular_pattern() {
        let bottom = r#"\bottom{SortS{}}()"#;
        let top = r#"\top{SortS{}}()"#;
        let regular = "a{}()";
        let cases = [
            (bottom, bottom, "valid", "Bottom"),
            (bottom, top, "valid", "Bottom"),
            (bottom, regular, "valid", "Bottom"),
            (regular, bottom, "invalid", "Bottom"),
            (regular, top, "valid", "Top"),
            (regular, regular, "valid", "Top"),
        ];
        let mut backend = backend();

        for (antecedent, consequent, status, predicate) in cases {
            let result = backend
                .implies(ImplicationRequest {
                    antecedent: kore(antecedent),
                    consequent: kore(consequent),
                    module_name: None,
                    schema_version: BACKEND_SCHEMA_VERSION,
                })
                .unwrap_or_else(|error| panic!("{antecedent} => {consequent} returned {error}"));
            let result = serde_json::to_value(result).unwrap();
            assert_eq!(result["status"], status, "{result:#}");
            assert_eq!(
                result["condition"]["predicate"]["term"]["tag"], predicate,
                "{result:#}"
            );
            assert_eq!(
                result["condition"]["substitution"]["term"]["tag"], "Top",
                "{result:#}"
            );
            assert_eq!(
                result["condition"]["witnesses"]["term"]["tag"], "Top",
                "{result:#}"
            );
        }

        for consequent in [bottom, top, regular] {
            let error = backend
                .implies(ImplicationRequest {
                    antecedent: kore(top),
                    consequent: kore(consequent),
                    module_name: None,
                    schema_version: BACKEND_SCHEMA_VERSION,
                })
                .expect_err("a top antecedent must be rejected");
            assert!(error.to_string().contains("function-like"), "{error}");
        }
    }

    #[test]
    fn persistent_backend_short_circuits_a_not_consequent() {
        let result = backend()
            .implies(ImplicationRequest {
                antecedent: kore("a{}()"),
                consequent: kore(r#"\not{SortS{}}(a{}())"#),
                module_name: None,
                schema_version: BACKEND_SCHEMA_VERSION,
            })
            .unwrap();
        assert_eq!(result.status, "invalid");
        assert!(result.condition.is_none());
    }

    #[test]
    fn implies_rejects_internalized_sort_mismatch() {
        let error = backend()
            .implies(ImplicationRequest {
                antecedent: kore("a{}()"),
                consequent: kore("t{}()"),
                module_name: None,
                schema_version: BACKEND_SCHEMA_VERSION,
            })
            .unwrap_err();
        assert!(
            error
                .to_string()
                .contains("sorts differ after internalization"),
            "{error}"
        );
    }

    #[test]
    fn persistent_implication_conditions_keep_bindings_separate() {
        use k_rust_backend::{
            implication::ImplicationCondition, substitution::Substitution, term::Variable,
        };

        let definition = backend().session.definition(None).unwrap();
        let sort = Sort::simple("SortS");
        let condition = ImplicationCondition {
            predicates: vec![Predicate::False],
            substitution: Substitution::from([(
                Variable::new("X", sort.clone()),
                definition
                    .admit_unverified(&parse_pattern("a{}()").unwrap(), &[])
                    .internalize_term()
                    .unwrap(),
            )]),
            witnesses: Substitution::from([(
                Variable::new("Y", sort.clone()),
                definition
                    .admit_unverified(&parse_pattern("b{}()").unwrap(), &[])
                    .internalize_term()
                    .unwrap(),
            )]),
        };

        let output = condition_pattern(&condition, &sort).unwrap();
        assert_eq!(output["predicate"]["term"]["tag"], "Bottom", "{output:#}");
        assert_eq!(
            output["substitution"]["term"]["tag"], "Equals",
            "{output:#}"
        );
        assert_eq!(
            output["substitution"]["term"]["first"]["name"], "X",
            "{output:#}"
        );
        assert_eq!(output["witnesses"]["term"]["tag"], "Equals", "{output:#}");
        assert_eq!(
            output["witnesses"]["term"]["first"]["name"], "Y",
            "{output:#}"
        );
    }

    #[test]
    fn persistent_implication_results_advertise_schema_version_two() {
        let result = backend()
            .implies(ImplicationRequest {
                antecedent: kore("a{}()"),
                consequent: kore("a{}()"),
                module_name: None,
                schema_version: BACKEND_SCHEMA_VERSION,
            })
            .unwrap();
        let result = serde_json::to_value(result).unwrap();

        assert_eq!(result["schemaVersion"], 2, "{result:#}");
    }

    #[test]
    fn persistent_backend_names_and_structures_unsupported_hook_failures() {
        let state = kore(r#"missing{}(\dv{SortState{}}("value"))"#);
        let mut backend = Backend::new(
            UNSUPPORTED_HOOK_DEFINITION,
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();

        let execution = backend.execute(ExecuteRequest::new(state.clone())).unwrap();
        assert_eq!(
            execution.leaves[0].reason,
            HaltReasonOutput::UnsupportedHook
        );
        let encoded_execution = serde_json::to_value(&execution).unwrap();
        assert_eq!(encoded_execution["leaves"][0]["reason"], "unsupported-hook");
        assert!(
            execution.leaves[0]
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("TEST.missing")),
            "{:#?}",
            execution.leaves[0]
        );

        let search = backend.search(SearchRequest::new(state)).unwrap();
        let encoded = serde_json::to_value(search).unwrap();
        let encoded = encoded.to_string();
        assert!(
            encoded.contains(r#""kind":"unsupported-hook""#),
            "{encoded}"
        );
        assert!(encoded.contains("TEST.missing"), "{encoded}");
    }

    #[test]
    fn persistent_backend_searches_states_and_reports_bounds() {
        let mut backend = backend();
        let result = backend.search(SearchRequest::new(kore("a{}()"))).unwrap();
        assert_eq!(result.schema_version, BACKEND_SCHEMA_VERSION);
        assert_eq!(result.modality, ResultModalityOutput::StateSet);
        assert_eq!(result.states.len(), 1);
        assert_eq!(text(result.states[0].state.clone()), "c{}()");
        assert!(result.incomplete.is_empty());

        let bounded = backend
            .search(SearchRequest {
                max_results: Some(0),
                ..SearchRequest::new(kore("a{}()"))
            })
            .unwrap();
        assert!(bounded.states.is_empty());
        assert_eq!(bounded.incomplete, [IncompleteSearchOutput::ResultBound]);
    }

    #[test]
    fn persistent_backend_searches_deterministic_path_witnesses() {
        let request = SearchRequest::new(kore("initial{}()"));
        let mut backend =
            Backend::new(DIAMOND_DEFINITION, "DIAMOND", BackendOptions::default()).unwrap();
        let first = backend.search_paths(request.clone()).unwrap();
        let second = backend.search_paths(request).unwrap();

        assert_eq!(first.modality, ResultModalityOutput::PathSet);
        assert_eq!(first.witnesses.len(), 2);
        assert_eq!(first.witnesses, second.witnesses);
        let paths = first
            .witnesses
            .iter()
            .map(|witness| {
                witness
                    .id
                    .iter()
                    .map(|transition| transition.rule.as_str())
                    .collect::<Vec<_>>()
            })
            .collect::<Vec<_>>();
        assert!(paths.contains(&vec!["initial-left", "left-merged"]));
        assert!(paths.contains(&vec!["initial-right", "right-merged"]));
    }

    #[test]
    fn persistent_backend_searches_patterns_in_both_modalities() {
        let mut backend = backend();
        let state_set = backend
            .search_pattern(SearchPatternRequest::new(kore("a{}()"), kore("c{}()")))
            .unwrap();
        assert_eq!(state_set.modality, ResultModalityOutput::StateSet);
        assert_eq!(state_set.matches.len(), 1);
        assert_eq!(text(state_set.matches[0].state.state.clone()), "c{}()");

        let mut diamond =
            Backend::new(DIAMOND_DEFINITION, "DIAMOND", BackendOptions::default()).unwrap();
        let path_set = diamond
            .search_pattern_paths(SearchPatternRequest::new(
                kore("initial{}()"),
                kore("merged{}()"),
            ))
            .unwrap();
        assert_eq!(path_set.modality, ResultModalityOutput::PathSet);
        assert_eq!(path_set.matches.len(), 2);
        assert!(
            path_set
                .matches
                .iter()
                .all(|found| found.witness.id.len() == 2)
        );
    }

    /// The target of a pattern search is internalized without the executable check, so it may
    /// apply an alias that drops a variable the client wrote. The search still mints no name
    /// spelled like it: the rule's existential `Y` is first minted `Ex#Y!0`, which is spelled
    /// `Ex-hY-b0` like the variable the target's `ignore` drops.
    #[test]
    fn pattern_searches_mint_apart_from_target_variables_an_alias_drops() {
        const DEFINITION: &str = r#"[]
module DROP
  sort S{} []
  symbol a{}() : S{} [constructor{}(), functional{}()]
  symbol c{}(S{}) : S{} [constructor{}(), functional{}()]
  symbol pair{}(S{}, S{}) : S{} [constructor{}(), functional{}()]
  alias ignore{}(S{}) : S{} where ignore{}(V:S{}) := a{}() []
  axiom{} \rewrites{S{}}(
    \and{S{}}(c{}(Z:S{}), \top{S{}}()),
    \and{S{}}(pair{}(Y:S{}, a{}()), \top{S{}}())
  ) [label{}("mint")]
endmodule []"#;
        let mut backend = Backend::new(DEFINITION, "DROP", BackendOptions::default()).unwrap();
        let request = SearchPatternRequest::new(
            kore("c{}(a{}())"),
            kore("pair{}(W:S{}, ignore{}(Ex-hY-b0:S{}))"),
        );
        let states =
            serde_json::to_string(&backend.search_pattern(request.clone()).unwrap()).unwrap();
        let paths = serde_json::to_string(&backend.search_pattern_paths(request).unwrap()).unwrap();
        for response in [states, paths] {
            assert!(response.contains("Ex-hY-b"), "{response}");
            assert!(!response.contains("Ex-hY-b0"), "{response}");
        }
    }

    #[test]
    fn observed_searches_expose_filtered_transition_streams_atomically() {
        let request = SearchRequest::new(kore("a{}()"));
        let mut backend = backend();
        let observed = backend
            .search_observed(ObservedRequest {
                request: request.clone(),
                rules: Some(vec!["a-to-b".into()]),
            })
            .unwrap();
        assert_eq!(observed.states[0].branch.len(), 2);
        let [ObservationEventOutput::Transition { id, .. }] =
            observed.states[0].observations.as_slice()
        else {
            panic!("expected one filtered transition observation")
        };
        assert_eq!(id.rule, "a-to-b");

        let error = backend
            .search_observed(ObservedRequest {
                request,
                rules: Some(vec!["a-to-b".into(), "missing".into()]),
            })
            .unwrap_err();
        assert!(
            error.to_string().contains("has the id 'missing'"),
            "{error}"
        );
    }

    #[test]
    fn execute_preserves_effects_and_observed_execution_attributes_them() {
        let request = ExecuteRequest::new(kore(r#"log{}(\dv{SortString{}}("one line"))"#));
        let mut backend = Backend::new(LOG_DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let ordinary = backend.execute(request.clone()).unwrap();
        assert_eq!(
            ordinary.effects,
            [EffectOutput::UserLog {
                message: "one line".into()
            }]
        );
        assert_eq!(ordinary.leaves.len(), 1);
        assert_eq!(ordinary.leaves[0].effects, ordinary.effects);
        assert!(ordinary.leaves[0].observations.is_empty());

        let observed = backend
            .execute_observed(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap();
        let [
            ObservationEventOutput::Evaluation {
                rule,
                class,
                anchor,
                effects,
                ..
            },
        ] = observed.leaves[0].observations.as_slice()
        else {
            panic!("expected one builtin evaluation observation")
        };
        assert_eq!(rule, "builtin:IO.logString");
        assert_eq!(*class, EvaluationClassOutput::Builtin);
        assert_eq!(*anchor, 0);
        assert_eq!(effects, &ordinary.effects);
        assert_eq!(observed.leaves[0].effects, ordinary.leaves[0].effects);
    }

    #[test]
    fn execute_exposes_each_branches_effects_without_observation() {
        let request = ExecuteRequest::new(kore("initial{}()"));
        let mut backend = Backend::new(
            EFFECTFUL_BRANCH_DEFINITION,
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();
        let ordinary = backend.execute(request.clone()).unwrap();
        assert_eq!(ordinary.leaves.len(), 2);
        assert!(ordinary.effects.is_empty());
        assert!(
            ordinary
                .leaves
                .iter()
                .all(|leaf| leaf.observations.is_empty())
        );
        let branch_effects = |result: &ExecutionResult| {
            let mut effects = result
                .leaves
                .iter()
                .map(|leaf| (leaf.trace[0].label.clone().unwrap(), leaf.effects.clone()))
                .collect::<Vec<_>>();
            effects.sort_by(|left, right| left.0.cmp(&right.0));
            effects
        };
        assert_eq!(
            branch_effects(&ordinary),
            [
                (
                    "left".into(),
                    vec![EffectOutput::UserLog {
                        message: "left".into()
                    }]
                ),
                (
                    "right".into(),
                    vec![EffectOutput::UserLog {
                        message: "right".into()
                    }]
                ),
            ]
        );

        let observed = backend
            .execute_observed(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap();
        assert_eq!(branch_effects(&observed), branch_effects(&ordinary));
        assert!(observed.effects.is_empty());
    }

    #[test]
    fn observation_preserves_facade_leaves_order_and_filter_independent_identities() {
        let mut backend = Backend::new(
            OBSERVATION_ERASURE_DEFINITION,
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();
        let erase = |mut result: ExecutionResult| {
            for leaf in &mut result.leaves {
                leaf.branch.clear();
                leaf.observations.clear();
            }
            serde_json::to_value(result).unwrap()
        };

        for (modality, expected_leaves) in [
            (ResultModalityOutput::StateSet, 1),
            (ResultModalityOutput::PathSet, 2),
        ] {
            let request = ExecuteRequest {
                result_modality: modality,
                ..ExecuteRequest::new(kore("initial{}()"))
            };
            let plain = backend.execute(request.clone()).unwrap();
            let all = backend
                .execute_observed(ObservedRequest {
                    request: request.clone(),
                    rules: None,
                })
                .unwrap();
            let selected = backend
                .execute_observed(ObservedRequest {
                    request: request.clone(),
                    rules: Some(vec!["left".into()]),
                })
                .unwrap();
            let none = backend
                .execute_observed(ObservedRequest {
                    request,
                    rules: Some(vec![]),
                })
                .unwrap();

            assert_eq!(plain.leaves.len(), expected_leaves, "{modality:?}");
            assert!(plain.leaves.iter().all(|leaf| leaf.branch.is_empty()));
            assert!(plain.leaves.iter().all(|leaf| leaf.observations.is_empty()));
            assert!(plain.leaves.iter().all(|leaf| leaf.effects
                == [EffectOutput::UserLog {
                    message: "same".into(),
                }]));
            let expected = erase(plain);
            for observed in [&all, &selected, &none] {
                assert_eq!(erase(observed.clone()), expected, "{modality:?}");
                assert_eq!(
                    observed
                        .leaves
                        .iter()
                        .map(|leaf| &leaf.branch)
                        .collect::<Vec<_>>(),
                    all.leaves
                        .iter()
                        .map(|leaf| &leaf.branch)
                        .collect::<Vec<_>>(),
                    "{modality:?}"
                );
            }
            assert!(
                all.leaves
                    .iter()
                    .all(|leaf| leaf.depth > 0 && !leaf.branch.is_empty())
            );
            assert!(all.leaves.iter().any(|leaf| !leaf.observations.is_empty()));
            assert!(none.leaves.iter().all(|leaf| leaf.observations.is_empty()));
        }
    }

    #[test]
    fn observed_path_set_execution_keeps_converging_paths_apart() {
        let request = |modality: &str| {
            serde_json::from_value::<ExecuteRequest>(serde_json::json!({
                "state": json("initial{}()"),
                "resultModality": modality,
            }))
            .unwrap()
        };
        let labels = |leaf: &ExecutionLeaf| {
            leaf.observations
                .iter()
                .filter_map(|event| match event {
                    ObservationEventOutput::Transition { rule_label, .. } => rule_label.clone(),
                    _ => None,
                })
                .collect::<Vec<_>>()
        };
        let mut backend =
            Backend::new(DIAMOND_DEFINITION, "DIAMOND", BackendOptions::default()).unwrap();

        let state_set = backend
            .execute_observed(ObservedRequest {
                request: request("state-set"),
                rules: None,
            })
            .unwrap();
        assert_eq!(state_set.modality, ResultModalityOutput::StateSet);
        assert_eq!(state_set.leaves.len(), 1);
        assert_eq!(
            serde_json::to_value(&state_set).unwrap()["modality"],
            "state-set"
        );

        let path_set = backend
            .execute_observed(ObservedRequest {
                request: request("path-set"),
                rules: None,
            })
            .unwrap();
        assert_eq!(path_set.modality, ResultModalityOutput::PathSet);
        assert_eq!(
            serde_json::to_value(&path_set).unwrap()["modality"],
            "path-set"
        );
        let [left, right] = path_set.leaves.as_slice() else {
            panic!("expected one leaf per path: {:#?}", path_set.leaves);
        };
        for leaf in [left, right] {
            assert_eq!(text(leaf.state.clone()), "merged{}()");
            // Compared on the wire so the check is independent of the Rust type of `reason`.
            assert_eq!(serde_json::to_value(leaf).unwrap()["reason"], "stuck");
        }
        assert_ne!(left.branch, right.branch);
        assert_eq!(labels(left), ["initial-left", "left-merged"]);
        assert_eq!(labels(right), ["initial-right", "right-merged"]);

        let default = backend
            .execute(ExecuteRequest::new(kore("initial{}()")))
            .unwrap();
        assert_eq!(default.modality, ResultModalityOutput::StateSet);
        assert_eq!(default.leaves.len(), 1);
    }

    #[test]
    fn observed_execution_anchors_a_successor_evaluation_after_its_rewrite() {
        const EVALUATING_DEFINITION: &str = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortState{} []
                symbol start{}() : SortState{} [constructor{}()]
                symbol next{}(SortS{}) : SortState{} [constructor{}()]
                symbol value{}() : SortS{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \top{R}()),
                    \equals{SortS{}, R}(
                        value{}(),
                        \and{SortS{}}(\dv{SortS{}}("value"), \top{SortS{}}())
                    )
                ) [label{}("value-equation")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    next{}(value{}())
                ) [label{}("step")]
            endmodule []"#;
        let mut backend =
            Backend::new(EVALUATING_DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let request = ExecuteRequest::new(kore("start{}()"));
        let ordinary = backend.execute(request.clone()).unwrap();

        let observed = backend
            .execute_observed(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap();
        let [leaf] = observed.leaves.as_slice() else {
            panic!("expected one leaf")
        };
        let [
            ObservationEventOutput::Transition { id, class, .. },
            ObservationEventOutput::Evaluation {
                rule,
                class: evaluation_class,
                rule_label,
                anchor,
                after,
                ..
            },
        ] = leaf.observations.as_slice()
        else {
            panic!("expected a rewrite then its successor's evaluation: {leaf:?}")
        };
        assert_eq!(leaf.branch.as_slice(), std::slice::from_ref(id));
        assert_eq!(id.rule, "step");
        assert_eq!(*class, TransitionClassOutput::Rewrite);
        assert_eq!(rule, "value-equation");
        assert_eq!(*evaluation_class, EvaluationClassOutput::FunctionEquation);
        assert_eq!(rule_label.as_deref(), Some("value-equation"));
        assert_eq!(*anchor, 1);
        assert_eq!(text(after.clone()), r#"next{}(\dv{SortS{}}("value"))"#);
        assert_eq!(
            text(leaf.state.clone()),
            text(ordinary.leaves[0].state.clone())
        );

        let wire = serde_json::to_value(&leaf.observations[1]).unwrap();
        assert_eq!(wire["kind"], "evaluation");
        assert_eq!(wire["class"], "function-equation");
        assert_eq!(wire["ruleLabel"], "value-equation");
        assert_eq!(wire["anchor"], 1);
        assert_eq!(
            serde_json::from_value::<ObservationEventOutput>(wire).unwrap(),
            leaf.observations[1]
        );
    }

    #[test]
    fn observed_execution_selects_function_equation_without_its_rewrite() {
        const DEFINITION: &str = r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                sort SortBool{} [hasDomainValues{}()]
                sort SortState{} []
                symbol start{}() : SortState{} [constructor{}()]
                symbol done{}(SortBool{}) : SortState{} [constructor{}()]
                symbol isZero{}(SortS{}) : SortBool{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(
                        \top{R}(),
                        \and{R}(
                            \in{SortS{}, R}(Z:SortS{}, \dv{SortS{}}("z")),
                            \top{R}()
                        )
                    ),
                    \equals{SortBool{}, R}(
                        isZero{}(Z:SortS{}),
                        \and{SortBool{}}(\dv{SortBool{}}("true"), \top{SortBool{}}())
                    )
                ) [label{}("is-zero-z")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(start{}(), \top{SortState{}}()),
                    done{}(isZero{}(\dv{SortS{}}("z")))
                ) [label{}("step")]
            endmodule []"#;
        let mut backend = Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let request = ExecuteRequest::new(kore("start{}()"));
        let selected = backend
            .execute_observed(ObservedRequest {
                request: request.clone(),
                rules: Some(vec!["is-zero-z".into()]),
            })
            .unwrap();
        let [leaf] = selected.leaves.as_slice() else {
            panic!("expected one leaf: {selected:?}");
        };
        assert_eq!(leaf.branch.len(), 1);
        assert_eq!(leaf.branch[0].rule, "step");
        let [
            ObservationEventOutput::Evaluation {
                rule,
                class,
                anchor,
                ..
            },
        ] = leaf.observations.as_slice()
        else {
            panic!("expected only the selected equation: {leaf:?}");
        };
        assert_eq!(rule, "is-zero-z");
        assert_eq!(*class, EvaluationClassOutput::FunctionEquation);
        assert_eq!(*anchor, 1);
        assert_eq!(
            text(leaf.state.clone()),
            r#"done{}(\dv{SortBool{}}("true"))"#
        );

        let selected = backend
            .execute_observed(ObservedRequest {
                request,
                rules: Some(vec!["step".into(), "is-zero-z".into()]),
            })
            .unwrap();
        assert!(matches!(
            selected.leaves[0].observations.as_slice(),
            [
                ObservationEventOutput::Transition { .. },
                ObservationEventOutput::Evaluation { .. }
            ]
        ));
    }

    /// Two written copies of one rule, in the shape K-in-K2's `duplicate_unlabelled.k` fixture has.
    const DUPLICATE_UNLABELLED: &str = "module DUPLICATE_UNLABELLED-SYNTAX
  syntax S ::= \"x\" [symbol(x)]
             | \"y\" [symbol(y)]
endmodule

module DUPLICATE_UNLABELLED
  imports DUPLICATE_UNLABELLED-SYNTAX
  imports BASIC-K
  imports INT-SYNTAX
  configuration <k> .K </k>

  rule x => y
  rule x => y
endmodule
";

    /// `<k> x </k>` in the generated configuration of [`DUPLICATE_UNLABELLED`].
    const DUPLICATE_UNLABELLED_STATE: &str = r#"Lbl'-LT-'generatedTop'-GT-'{}(
        Lbl'-LT-'k'-GT-'{}(kseq{}(inj{SortS{}, SortKItem{}}(Lblx{}()), dotk{}())),
        Lbl'-LT-'generatedCounter'-GT-'{}(\dv{SortInt{}}("0"))
    )"#;

    /// The source-compiled execution definition, internalized as `krust krun` does.
    fn source_definition(source: &str, module: &str) -> BackendDefinition {
        use crate::{
            builtin::embedded,
            kompile::{CompilationBackend, CompileOptions, compile_loaded_definition},
            outer::{LoadOptions, ResolvedSource, load_with_options},
        };

        let mut resolver = |_: &str, required: &str| {
            embedded(required).ok_or_else(|| format!("unexpected require {required}"))
        };
        let loaded = load_with_options(
            ResolvedSource::new("duplicate.k", source),
            module,
            &mut resolver,
            &LoadOptions {
                implicit_sources: vec![embedded("prelude.md").unwrap()],
                excluded_module_attributes: vec![
                    CompilationBackend::Rust.excluded_module_attribute().into(),
                ],
                ..LoadOptions::default()
            },
        )
        .unwrap();
        let compiled = compile_loaded_definition(&loaded, CompileOptions::default()).unwrap();
        let syntax = parse_definition(&compiled.definition_kore).unwrap();
        // The main module is emitted last, under its KORE-encoded name.
        let main_module = syntax.modules.last().unwrap().name.clone();
        Backend::internalize_source_definition(
            &syntax,
            &main_module,
            &compiled.execution_rewrite_order,
        )
        .unwrap()
    }

    /// The `UNIQUE_ID` and origin locations of the rewrite rule whose first origin is on `line`.
    fn rule_on_line(definition: &BackendDefinition, line: usize) -> (String, Vec<String>) {
        let prefix = format!("Location({line},");
        let rules = definition
            .rewrite_theory()
            .values()
            .flat_map(|priorities| priorities.values())
            .flatten()
            .filter(|stored| {
                stored.rule.attributes.origins[0]
                    .location
                    .as_deref()
                    .is_some_and(|location| location.starts_with(&prefix))
            })
            .collect::<Vec<_>>();
        let [stored] = rules.as_slice() else {
            panic!("expected one stored rule written on line {line}: {rules:?}");
        };
        let attributes = &stored.rule.attributes;
        (
            attributes.unique_id.clone(),
            attributes
                .origins
                .iter()
                .map(|origin| origin.location.clone().unwrap())
                .collect(),
        )
    }

    #[test]
    fn source_duplicated_rule_executes_and_is_observed_as_one_rule() {
        let single_source = DUPLICATE_UNLABELLED.replacen("  rule x => y\n", "", 1);
        let single = source_definition(&single_source, "DUPLICATE_UNLABELLED");
        let duplicated = source_definition(DUPLICATE_UNLABELLED, "DUPLICATE_UNLABELLED");

        let (single_id, single_origins) = rule_on_line(&single, 12);
        let (id, origins) = rule_on_line(&duplicated, 12);
        assert_eq!(single_origins, ["Location(12,3,12,14)"]);
        assert_eq!(origins, ["Location(12,3,12,14)", "Location(13,3,13,14)"]);
        assert_eq!(id, single_id);

        let request = ExecuteRequest {
            stop_at_branch: true,
            ..ExecuteRequest::new(kore(DUPLICATE_UNLABELLED_STATE))
        };
        let mut outcomes = Vec::new();
        for definition in [single, duplicated] {
            let mut backend =
                Backend::from_internalized(definition, BackendOptions::default()).expect("backend");
            let result = backend.execute(request.clone()).unwrap();
            let [leaf] = result.leaves.as_slice() else {
                panic!("expected one leaf: {:?}", result.leaves);
            };
            assert_ne!(leaf.reason, HaltReasonOutput::Branch);
            assert!(text(leaf.state.clone()).contains("Lbly{}()"));
            assert_eq!(leaf.depth, 1);

            let observed = backend
                .execute_observed(ObservedRequest {
                    request: request.clone(),
                    rules: Some(vec![id.clone()]),
                })
                .unwrap();
            let [observed_leaf] = observed.leaves.as_slice() else {
                panic!("expected one observed leaf: {:?}", observed.leaves);
            };
            let [ObservationEventOutput::Transition { id: transition, .. }] =
                observed_leaf.observations.as_slice()
            else {
                panic!(
                    "expected one rule application: {:?}",
                    observed_leaf.observations
                );
            };
            assert_eq!(transition.rule, id);
            outcomes.push((
                text(leaf.state.clone()),
                leaf.reason,
                serde_json::to_value(&observed_leaf.observations).unwrap(),
            ));
        }
        assert_eq!(outcomes[0], outcomes[1]);
    }

    #[test]
    fn capabilities_advertise_search_and_observation() {
        let capabilities = backend().capabilities();
        assert!(capabilities.search);
        assert!(capabilities.observation);
    }

    #[test]
    fn prove_request_budget_reaches_the_prover() {
        let mut chain = String::new();
        for index in 0..=128 {
            chain.push_str(&format!(
                "symbol chain{index}{{}}() : SortS{{}} [function{{}}()]\n"
            ));
        }
        for index in 0..128 {
            let next = index + 1;
            chain.push_str(&format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortS{{}}, R}}(
                        chain{index}{{}}(),
                        \and{{SortS{{}}}}(chain{next}{{}}(), \top{{SortS{{}}}}())
                    )
                ) [label{{}}("chain-{index}"), simplification{{}}()]
                "#
            ));
        }
        chain.push_str(
            r#"
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortS{}, R}(
                        chain128{}(),
                        \and{SortS{}}(a{}(), \top{SortS{}}())
                    )
                ) [label{}("chain-done"), simplification{}()]
            "#,
        );
        let definition = format!(
            r#"[]
            module MAIN
                sort SortS{{}} []
                symbol a{{}}() : SortS{{}} [constructor{{}}()]
                symbol c{{}}() : SortS{{}} [constructor{{}}()]
                alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                {chain}
                axiom{{}} \rewrites{{SortS{{}}}}(
                    \and{{SortS{{}}}}(
                        a{{}}(),
                        \equals{{SortS{{}}, SortS{{}}}}(chain0{{}}(), a{{}}())
                    ),
                    c{{}}()
                ) [label{{}}("conditional")]
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}()),
                    weakAlwaysFinally{{SortS{{}}}}(c{{}}())
                ) [label{{}}("budgeted-claim")]
            endmodule []"#
        );
        let mut backend = Backend::new(&definition, "MAIN", BackendOptions::default()).unwrap();

        let result = backend
            .prove(ProveRequest {
                max_simplification_iterations: 1,
                ..ProveRequest::default()
            })
            .expect("budget exhaustion should be represented as a proof result");

        // Without SMT, an exhausted side condition remains indeterminate; with the native
        // solver the leaf is stuck, but its constraint holds the unevaluated `chain0()`, so it
        // fails the claim without certifying a refutation. Neither may establish the claim.
        assert!(
            matches!(result.status.as_str(), "failed" | "indeterminate"),
            "{result:#?}"
        );
        assert!(
            result
                .leaves
                .iter()
                .all(|leaf| !leaf.outcome.contains("IterationLimit")),
            "{result:#?}"
        );
        let completed = backend
            .prove(ProveRequest {
                max_simplification_iterations: 256,
                ..ProveRequest::default()
            })
            .unwrap();
        assert_eq!(completed.status, "proven", "{completed:#?}");
    }

    #[test]
    fn added_modules_are_available_to_later_calls() {
        let mut backend = backend();
        let module = r#"module EXTRA
            import MAIN []
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(c{}(), \top{SortS{}}()),
                \and{SortS{}}(a{}(), \top{SortS{}}())
            ) [label{}("c-to-a")]
        endmodule []"#;
        backend.add_module(module, true).unwrap();
        let execution = backend
            .execute(ExecuteRequest {
                module_name: Some("EXTRA".into()),
                max_depth: Some(1),
                ..ExecuteRequest::new(kore("c{}()"))
            })
            .unwrap();
        assert_eq!(text(execution.leaves[0].state.clone()), "a{}()");
    }

    /// KORE JSON terms `levels` deep that decode but are not patterns of the definition: a `\not`
    /// chain whose leaf applies an undeclared symbol, a chain of an undeclared symbol, and a
    /// domain value at a deep undeclared sort.
    fn deep_invalid_kore_json(levels: usize) -> [String; 3] {
        let sort = r#"{"tag":"SortApp","name":"SortS","args":[]}"#;
        let undefined = r#"{"tag":"App","name":"undefined","sorts":[],"args":[]}"#;
        let constant = r#"{"tag":"App","name":"a","sorts":[],"args":[]}"#;
        let term = |prefix: &str, leaf: &str, suffix: &str| {
            format!(
                r#"{{"format":"KORE","version":1,"term":{}{leaf}{}}}"#,
                prefix.repeat(levels),
                suffix.repeat(levels)
            )
        };
        let deep_sort = format!(
            "{}{sort}{}",
            r#"{"tag":"SortApp","name":"SortMissing","args":["#.repeat(levels),
            "]}".repeat(levels)
        );
        [
            term(
                &format!(r#"{{"tag":"Not","sort":{sort},"arg":"#),
                undefined,
                "}",
            ),
            term(
                r#"{"tag":"App","name":"nosuch","sorts":[],"args":["#,
                constant,
                "]}",
            ),
            format!(
                r#"{{"format":"KORE","version":1,"term":{{"tag":"DV","sort":{deep_sort},"value":"1"}}}}"#
            ),
        ]
    }

    /// The stack of Node's main thread, which the Node-API binding runs the facade on.
    const NODE_MAIN_STACK: usize = 8 << 20;

    /// Levels beyond what `NODE_MAIN_STACK` holds for the facade's passes in either build: a
    /// state of applications overflows such a thread at about 600 levels unoptimized (opt-level
    /// 0, the `debugging` profile) and 8,000 in a release build when the passes run on it
    /// directly.
    const BEYOND_THE_THREAD: usize = 10_000;

    fn on_thread<R: Send + 'static>(stack: usize, work: impl FnOnce() -> R + Send + 'static) -> R {
        std::thread::Builder::new()
            .stack_size(stack)
            .spawn(work)
            .expect("worker should spawn")
            .join()
            .expect("worker should finish")
    }

    /// Every route of the facade that the Node-API and WebAssembly hosts call, run on `deep`,
    /// each with a shallow pattern where the route takes two.
    fn every_route(backend: &mut Backend, deep: &KorePattern) -> Vec<Result<(), BackendError>> {
        let shallow = kore("a{}()");
        let routes = vec![
            backend
                .execute_json(ExecuteRequest {
                    max_depth: Some(0),
                    ..ExecuteRequest::new(deep.clone())
                })
                .map(drop),
            backend
                .search_json(SearchRequest::new(deep.clone()))
                .map(drop),
            backend
                .search_pattern_json(SearchPatternRequest::new(deep.clone(), shallow.clone()))
                .map(drop),
            backend
                .search_pattern_json(SearchPatternRequest::new(shallow.clone(), deep.clone()))
                .map(drop),
            backend
                .simplify_json(PatternRequest::new(deep.clone()))
                .map(drop),
            backend
                .implies_json(ImplicationRequest::new(deep.clone(), shallow.clone()))
                .map(drop),
            backend
                .implies_json(ImplicationRequest::new(shallow, deep.clone()))
                .map(drop),
        ];
        // Without Z3, model generation reports its capability boundary before it reads the
        // pattern.
        #[cfg(feature = "z3-inference")]
        let routes = routes
            .into_iter()
            .chain([backend
                .get_model_json(PatternRequest::new(deep.clone()))
                .map(drop)])
            .collect();
        routes
    }

    /// A request beyond what Node's main thread holds that decodes but is not a pattern of the
    /// definition is answered on every route of the facade as a shallow one is, with the
    /// ordinary error its fault calls for where the route reads the fault, never with a refusal
    /// for want of stack: the backend provides the stack its passes need. One
    /// 10,000-level term is held at a time; unoptimized (opt-level 0, the `debugging` profile)
    /// each request touches about 120 MB of stack, and the test takes a few seconds.
    #[test]
    fn deep_invalid_requests_are_ordinary_errors_on_every_route() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend = backend();
            for (term, deep) in deep_invalid_kore_json(BEYOND_THE_THREAD).iter().enumerate() {
                let deep = deserialize_request::<PatternRequest>(&format!(r#"{{"state":{deep}}}"#))
                    .unwrap()
                    .state;
                let outcomes = every_route(&mut backend, &deep);
                assert!(outcomes[0].is_err(), "term {term} executes");
                for (route, outcome) in outcomes.into_iter().enumerate() {
                    if let Err(error) = outcome {
                        assert!(
                            !error
                                .to_string()
                                .contains("the backend provides for one operation"),
                            "term {term} route {route}: {error}"
                        );
                    }
                }
            }
            // The backend still serves ordinary requests.
            let execution = backend.execute(ExecuteRequest::new(kore("a{}()"))).unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        });
    }

    /// A request deeper than the largest stack the backend provides is refused with
    /// `InsufficientStack` on every route before any pass over it runs. One term that deep (about
    /// 700,000 levels at opt-level 1, a million in a release build, 175,000 unoptimized) is held
    /// at a time; at opt-level 1 the test peaks at about 930 MB of resident memory and takes about
    /// 8 s.
    #[test]
    fn requests_deeper_than_the_backend_provides_for_are_refused() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend = backend();
            for deep in deep_invalid_kore_json(k_rust_backend::nesting::max_depth() + 1) {
                let deep = deserialize_request::<PatternRequest>(&format!(r#"{{"state":{deep}}}"#))
                    .unwrap()
                    .state;
                for error in every_route(&mut backend, &deep) {
                    let error = error.expect_err("a request too deep is refused");
                    assert!(
                        error
                            .to_string()
                            .contains("the backend provides for one operation"),
                        "{error}"
                    );
                }
            }
            let execution = backend.execute(ExecuteRequest::new(kore("a{}()"))).unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        });
    }

    /// A module whose axiom is a `\not` chain beyond what Node's main thread holds is added
    /// when the chain is a well-formed predicate and is the ordinary error of its fault when it
    /// is over a symbol the definition does not declare; a chain deeper than the backend
    /// provides for is refused with `InsufficientStack`. One module of up to about 10 MB of text
    /// is held at a time; at opt-level 1 the test peaks at about 450 MB of resident memory and
    /// takes a few seconds.
    #[test]
    fn deep_modules_are_loaded_or_ordinary_errors() {
        on_thread(NODE_MAIN_STACK, || {
            let module = |levels: usize, leaf: &str| {
                let condition = format!(
                    "{}{leaf}{}",
                    r"\not{SortS{}}(".repeat(levels),
                    ")".repeat(levels)
                );
                format!(
                    r"module EXTRA import MAIN []
                        axiom{{}} \rewrites{{SortS{{}}}}(
                            \and{{SortS{{}}}}(c{{}}(), {condition}),
                            \and{{SortS{{}}}}(a{{}}(), \top{{SortS{{}}}}())
                        ) []
                    endmodule []"
                )
            };
            let mut backend = backend();
            let too_deep = k_rust_backend::nesting::max_depth() + 1;
            for (levels, leaf, refused) in [
                (BEYOND_THE_THREAD, "undefined{}()", false),
                (too_deep, "undefined{}()", true),
                (too_deep, r"\top{SortS{}}()", true),
            ] {
                let error = backend
                    .add_module(&module(levels, leaf), false)
                    .unwrap_err();
                assert_eq!(
                    error
                        .to_string()
                        .contains("the backend provides for one operation"),
                    refused,
                    "{error}"
                );
            }
            let id = backend
                .add_module(&module(BEYOND_THE_THREAD, r"\top{SortS{}}()"), false)
                .expect("a deep well-formed module is added");
            // An operation in the extended definition runs on the stack its deep rule needs.
            let execution = backend
                .execute(ExecuteRequest {
                    module_name: Some(id),
                    max_depth: Some(1),
                    ..ExecuteRequest::new(kore("c{}()"))
                })
                .unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "a{}()");
            let execution = backend.execute(ExecuteRequest::new(kore("a{}()"))).unwrap();
            assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");
        });
    }

    /// A definition whose rule `step` adds one `wrap` level under `go` each step.
    const DEEP_DEFINITION: &str = r#"[]
        module MAIN
            sort SortS{} []
            symbol a{}() : SortS{} [constructor{}(), functional{}()]
            symbol wrap{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            symbol go{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            axiom{} \rewrites{SortS{}}(
                \and{SortS{}}(go{}(X:SortS{}), \top{SortS{}}()),
                \and{SortS{}}(go{}(wrap{}(X:SortS{})), \top{SortS{}}())
            ) [label{}("step")]
        endmodule []"#;

    /// KORE JSON for `go` over `levels` applications of `wrap` over `a`, or the `wrap` chain
    /// alone.
    fn wrap_json(levels: usize, go: bool) -> String {
        let wrap = r#"{"tag":"App","name":"wrap","sorts":[],"args":["#;
        let leaf = r#"{"tag":"App","name":"a","sorts":[],"args":[]}"#;
        let chain = format!("{}{leaf}{}", wrap.repeat(levels), "]}".repeat(levels));
        let term = if go {
            format!(r#"{{"tag":"App","name":"go","sorts":[],"args":[{chain}]}}"#)
        } else {
            chain
        };
        format!(r#"{{"format":"KORE","version":1,"term":{term}}}"#)
    }

    /// Whether two KORE JSON texts denote the same pattern, compared without printing them.
    fn same_kore(left: &str, right: &str) -> bool {
        k_rust_kore::kore::json::from_str(left).unwrap()
            == k_rust_kore::kore::json::from_str(right).unwrap()
    }

    /// The states of the leaves of an execution response, as the KORE JSON text they carry.
    fn leaf_states(response: &str) -> Vec<String> {
        #[derive(Deserialize)]
        struct Response {
            leaves: Vec<Leaf>,
        }
        #[derive(Deserialize)]
        struct Leaf {
            state: Box<RawValue>,
        }
        serde_json::from_str::<Response>(response)
            .unwrap()
            .leaves
            .into_iter()
            .map(|leaf| leaf.state.get().to_owned())
            .collect()
    }

    /// A state of 6,000 applications, which ran on Node's main thread when the passes ran on
    /// the thread directly in a release build, still executes there: the backend provides the
    /// stack measured for it instead of refusing it. Unoptimized (opt-level 0, the `debugging`
    /// profile) the request touches about 70 MB of stack and takes well under a second.
    #[test]
    fn a_deep_state_executes_on_node_s_main_thread() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(DEEP_DEFINITION, "MAIN", BackendOptions::default()).unwrap();
            let request = deserialize_request::<ExecuteRequest>(&format!(
                r#"{{"state":{},"maxDepth":0}}"#,
                wrap_json(6_000, false)
            ))
            .unwrap();
            let response = backend.execute_json(request).unwrap();
            let [state] = leaf_states(&response).try_into().unwrap();
            assert!(same_kore(&state, &wrap_json(6_000, false)));
        });
    }

    /// The state an execution returns is accepted as the next request's state: `go` over 1,900
    /// applications steps 300 times on Node's main thread, and its 2,200-level result steps
    /// again from there.
    #[test]
    fn a_returned_state_is_accepted_again() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(DEEP_DEFINITION, "MAIN", BackendOptions::default()).unwrap();
            let mut state = wrap_json(1_900, true);
            for levels in [2_200, 2_500] {
                let request = deserialize_request::<ExecuteRequest>(&format!(
                    r#"{{"state":{state},"maxDepth":300}}"#
                ))
                .unwrap();
                let [leaf] = leaf_states(&backend.execute_json(request).unwrap())
                    .try_into()
                    .unwrap();
                assert!(same_kore(&leaf, &wrap_json(levels, true)), "{levels}");
                state = leaf;
            }
        });
    }

    /// `DEEP_DEFINITION` with the claim `deep`, that `go` over `levels` applications of `wrap`
    /// over `a` always reaches `a`.
    fn deep_claim_definition(levels: usize) -> String {
        let chain = format!(
            "go{{}}({}a{{}}(){})",
            "wrap{}(".repeat(levels),
            ")".repeat(levels)
        );
        DEEP_DEFINITION.replace(
            "endmodule []",
            &format!(
                r#"alias weakAlwaysFinally{{S}}(S) : S
                    where weakAlwaysFinally{{S}}(@X:S) := @X:S []
                claim{{}} \implies{{SortS{{}}}}(
                    \and{{SortS{{}}}}({chain}, \top{{SortS{{}}}}()),
                    weakAlwaysFinally{{SortS{{}}}}(a{{}}())
                ) [label{{}}("deep")]
            endmodule []"#
            ),
        )
    }

    /// A caller's stack on which a proof result held as `serde_json::Value` (`prove`) overflows
    /// when it is serialized there from about 800 levels of its leaf (the `dev` profile,
    /// opt-level 1), while `prove` itself completes on it at 2,000.
    const SMALL_STACK: usize = 256 << 10;

    /// Levels of a proof's leaf beyond what `SMALL_STACK` holds for the leaf as a value.
    const DEEP_PROOF_LEVELS: usize = 2_000;

    /// A proof whose leaf is 2,000 levels deep is written as text by `prove_json` on a 256 KiB
    /// thread: the operation writes the leaf's KORE inside the stack it provides, and the
    /// caller receives text it can drop on any thread. The test takes well under a second.
    #[test]
    fn a_deep_proof_result_is_written_inside_the_operation() {
        let definition = deep_claim_definition(DEEP_PROOF_LEVELS);
        let response = on_thread(SMALL_STACK, move || {
            let mut backend = Backend::new(&definition, "MAIN", BackendOptions::default()).unwrap();
            backend
                .prove_json(ProveRequest {
                    max_depth: Some(1),
                    ..ProveRequest::default()
                })
                .unwrap()
        });
        let [leaf] = leaf_states(&response).try_into().unwrap();
        assert!(same_kore(&leaf, &wrap_json(DEEP_PROOF_LEVELS + 1, true)));
    }

    /// `prove_json` writes the result `prove` returns.
    #[test]
    fn prove_json_writes_the_proof_result() {
        let mut backend =
            Backend::new(&deep_claim_definition(3), "MAIN", BackendOptions::default()).unwrap();
        let request = ProveRequest {
            max_depth: Some(1),
            ..ProveRequest::default()
        };
        let text = backend.prove_json(request.clone()).unwrap();
        let value = backend.prove(request).unwrap();
        assert_eq!(
            serde_json::from_str::<Value>(&text).unwrap(),
            serde_json::to_value(&value).unwrap()
        );
        assert_eq!(value.leaves.len(), 1, "{value:#?}");
    }

    /// An n-ary `\and` of term arguments is internalized as a chain of `n - 1` binary
    /// conjunctions, so a wide request is deep inside the backend: 50,000 conjuncts execute on
    /// Node's main thread, and 200,000 execute as well where the backend provides the stack
    /// for them (an optimized build) and are otherwise refused, never overflowing the thread.
    /// The requests take about 10 MB of text each; at opt-level 1 the test peaks at about 300 MB
    /// of resident memory and takes under a second.
    #[test]
    fn wide_conjunctions_execute_or_are_refused() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(DEEP_DEFINITION, "MAIN", BackendOptions::default()).unwrap();
            let constant = r#"{"tag":"App","name":"a","sorts":[],"args":[]}"#;
            for conjuncts in [50_000, 200_000] {
                let request = deserialize_request::<ExecuteRequest>(&format!(
                    r#"{{"state":{{"format":"KORE","version":1,"term":{{"tag":"And","sort":{{"tag":"SortApp","name":"SortS","args":[]}},"patterns":[{}]}}}},"maxDepth":0}}"#,
                    vec![constant; conjuncts].join(",")
                ))
                .unwrap();
                let outcome = backend.execute_json(request);
                if conjuncts <= k_rust_backend::nesting::max_depth() {
                    outcome.unwrap_or_else(|error| panic!("{conjuncts}: {error}"));
                } else {
                    let error = outcome.unwrap_err();
                    assert!(
                        error
                            .to_string()
                            .contains("the backend provides for one operation"),
                        "{error}"
                    );
                }
            }
        });
    }

    /// Ground functions whose simplification descends once per level of the term: `f` and `h`
    /// have no equations, `g` moves under each `w` it meets, and `len` counts a `cons` list,
    /// adding with the `INT.add` hook on the way back up.
    const FUNCTION_CHAINS: &str = r#"[]
        module MAIN
            sort SortS{} []
            sort SortL{} []
            hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
            symbol a{}() : SortS{} [constructor{}(), functional{}()]
            symbol w{}(SortS{}) : SortS{} [constructor{}(), functional{}()]
            symbol nil{}() : SortL{} [constructor{}(), functional{}()]
            symbol cons{}(SortS{}, SortL{}) : SortL{} [constructor{}(), functional{}()]
            symbol f{}(SortS{}) : SortS{} [function{}(), total{}()]
            symbol h{}(SortS{}, SortS{}) : SortS{} [function{}(), total{}()]
            symbol g{}(SortS{}) : SortS{} [function{}(), total{}()]
            symbol len{}(SortL{}) : SortInt{} [function{}(), total{}()]
            hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                [function{}(), total{}(), hook{}("INT.add")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortS{}, R}(X0:SortS{}, w{}(X:SortS{})), \top{R}())),
                \equals{SortS{}, R}(g{}(X0:SortS{}), \and{SortS{}}(w{}(g{}(X:SortS{})), \top{SortS{}}()))
            ) [label{}("g-w")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, nil{}()), \top{R}())),
                \equals{SortInt{}, R}(len{}(X0:SortL{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
            ) [label{}("len-nil")]
            axiom{R} \implies{R}(
                \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, cons{}(H:SortS{}, T:SortL{})), \top{R}())),
                \equals{SortInt{}, R}(
                    len{}(X0:SortL{}),
                    \and{SortInt{}}(intAdd{}(\dv{SortInt{}}("1"), len{}(T:SortL{})), \top{SortInt{}}())
                )
            ) [label{}("len-cons")]
        endmodule []"#;

    /// The KORE JSON term of `levels` nested applications of `symbol` around `leaf`, each with
    /// the arguments `before` ahead of the nested one and `after` behind it.
    fn nested(levels: usize, symbol: &str, before: &str, after: &str, leaf: &str) -> String {
        let open = format!(r#"{{"tag":"App","name":"{symbol}","sorts":[],"args":[{before}"#);
        let close = format!("{after}]}}");
        format!("{}{leaf}{}", open.repeat(levels), close.repeat(levels))
    }

    /// The simplifier descends once per level of these terms, so its frames are among the passes
    /// over internal terms that the stack the backend provides per level must hold. At 5,000
    /// levels each request needs more than Node's main thread in every build (the simplifier
    /// takes about 3 KiB per level in a release build), so the facade runs it on a segment of
    /// exactly the size `nesting::stack_for_depth` gives for its height: a simplifier whose
    /// frames per level outgrew the bound stops with `StackExhausted` there, which the exact
    /// results rule out, or overflows the segment and aborts the test binary. At opt-level 1 each
    /// request touches about 20 MB of stack and the test takes about a second.
    #[test]
    fn deep_function_chains_simplify_on_the_stack_the_backend_provides() {
        on_thread(NODE_MAIN_STACK, || {
            let mut backend =
                Backend::new(FUNCTION_CHAINS, "MAIN", BackendOptions::default()).unwrap();
            // Confined to the stack sized from the input, the bound under test.
            backend.set_simplification_stack_budget(0);
            let envelope = |term: &str| format!(r#"{{"format":"KORE","version":1,"term":{term}}}"#);
            let levels = 5_000;
            let a = nested(1, "a", "", "", "");
            let nil = nested(1, "nil", "", "", "");
            let chain = nested(levels, "f", "", "", &a);
            let binary = nested(levels, "h", "", &format!(",{a}"), &a);
            let g_over_w = nested(1, "g", "", "", &nested(levels, "w", "", "", &a));
            let w_over_g = nested(levels, "w", "", "", &nested(1, "g", "", "", &a));
            let list = nested(levels, "cons", &format!("{a},"), "", &nil);
            let len = nested(1, "len", "", "", &list);
            let count = format!(
                r#"{{"tag":"DV","sort":{{"tag":"SortApp","name":"SortInt","args":[]}},"value":"{levels}"}}"#
            );
            for (name, request, expected) in [
                ("f", &chain, &chain),
                ("h", &binary, &binary),
                ("g over w", &g_over_w, &w_over_g),
                ("len", &len, &count),
            ] {
                let request = deserialize_request::<PatternRequest>(&format!(
                    r#"{{"state":{}}}"#,
                    envelope(request)
                ))
                .unwrap();
                let simplified = backend
                    .simplify_json(request)
                    .unwrap_or_else(|error| panic!("{name}: {error}"));
                assert!(same_kore(&simplified, &envelope(expected)), "{name}");
            }
        });
    }

    /// `lenb` counts a `cons` list like `len`, but its result nests two additions above the
    /// count of the tail, so its simplification takes more stack per level of the list than the
    /// backend provides per level (about 5.6 KiB in a release build, 8.1 KiB at opt-level 1 and
    /// 35 KiB unoptimized, against 4, 6 and 24 KiB): on the segment the facade maps for 10,000
    /// levels it reaches its red zone with thousands of levels of the list still below it. Each
    /// level binds the rest of the list, whose definedness is then derived, and the request must
    /// end with the count or with `StackExhausted`, not abort. Before the definedness walk kept
    /// its work on the heap, debug builds aborted here with a segmentation fault inside it (the
    /// release build skips the walk on the `ceil_free` list; `definedness::tests` cover it).
    #[test]
    fn a_simplification_that_outgrows_the_stack_bound_stops_at_its_red_zone() {
        on_thread(NODE_MAIN_STACK, || {
            let definition = FUNCTION_CHAINS.replace(
                "endmodule []",
                r#"
                symbol lenb{}(SortL{}) : SortInt{} [function{}(), total{}()]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, nil{}()), \top{R}())),
                    \equals{SortInt{}, R}(lenb{}(X0:SortL{}), \and{SortInt{}}(\dv{SortInt{}}("0"), \top{SortInt{}}()))
                ) [label{}("lenb-nil")]
                axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortL{}, R}(X0:SortL{}, cons{}(H:SortS{}, T:SortL{})), \top{R}())),
                    \equals{SortInt{}, R}(
                        lenb{}(X0:SortL{}),
                        \and{SortInt{}}(
                            intAdd{}(\dv{SortInt{}}("1"), intAdd{}(\dv{SortInt{}}("0"), lenb{}(T:SortL{}))),
                            \top{SortInt{}}()
                        )
                    )
                ) [label{}("lenb-cons")]
                endmodule []"#,
            );
            let mut backend = Backend::new(&definition, "MAIN", BackendOptions::default()).unwrap();
            // Confined to the stack sized from the input, the bound under test.
            backend.set_simplification_stack_budget(0);
            let levels = BEYOND_THE_THREAD;
            let a = nested(1, "a", "", "", "");
            let nil = nested(1, "nil", "", "", "");
            let count = nested(
                1,
                "lenb",
                "",
                "",
                &nested(levels, "cons", &format!("{a},"), "", &nil),
            );
            let request = deserialize_request::<PatternRequest>(&format!(
                r#"{{"state":{{"format":"KORE","version":1,"term":{count}}}}}"#
            ))
            .unwrap();
            match backend.simplify_json(request) {
                Ok(simplified) => assert!(
                    same_kore(
                        &simplified,
                        &format!(
                            r#"{{"format":"KORE","version":1,"term":{{"tag":"DV","sort":{{"tag":"SortApp","name":"SortInt","args":[]}},"value":"{levels}"}}}}"#
                        )
                    ),
                    "{simplified}"
                ),
                Err(error) => assert!(
                    error.to_string().contains(
                        &StopCause::StackExhausted(k_rust_backend::stop::StackLimit::ThreadBudget(
                            0
                        ))
                        .to_string()
                    ),
                    "{error}"
                ),
            }
        });
    }

    #[cfg(not(feature = "z3-inference"))]
    #[test]
    fn portable_model_generation_reports_the_capability_boundary() {
        let error = backend()
            .get_model(PatternRequest::new(kore("a{}()")))
            .unwrap_err();
        assert!(error.to_string().contains("no Z3"));
    }
}
