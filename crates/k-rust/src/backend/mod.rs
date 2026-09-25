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
use k_rust_backend::substitution::Substitution;
use k_rust_backend::{
    definition::BackendDefinition,
    externalize,
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
    term::Sort,
    transition::ObservationOptions,
};
use serde::{Deserialize, Serialize};
use serde_json::Value;

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
#[serde(default, deny_unknown_fields, rename_all = "camelCase")]
pub struct ExecuteRequest {
    pub state: Value,
    pub module_name: Option<String>,
    pub max_depth: Option<u64>,
    pub max_breadth: Option<usize>,
    /// Maximum simplifier iterations per rewrite step.
    ///
    /// The bound counts simplification-rule, builtin, and symbolic rewriting. Determined ground
    /// function evaluation (a function equation on a variable-free redex with no residual
    /// condition) runs to its value, bounded only by the step deadline or cancellation and by
    /// the thread's stack, whose exhaustion is a typed error.
    /// Execution keeps a partially simplified term or the original constraints after exhaustion
    /// and records a backend diagnostic before continuing.
    pub max_simplification_iterations: usize,
    pub strategy: ExecutionStrategy,
    pub stop_at_branch: bool,
    pub cut_point_rules: Vec<String>,
    pub terminal_rules: Vec<String>,
    pub step_timeout_ms: Option<u64>,
    pub moving_average_timeout: bool,
    pub assume_state_defined: bool,
    pub schema_version: u32,
}

impl Default for ExecuteRequest {
    fn default() -> Self {
        Self {
            state: Value::Null,
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
pub struct ExecutionResult {
    pub leaves: Vec<ExecutionLeaf>,
    pub effects: Vec<EffectOutput>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub discarded: Vec<ObservationEventOutput>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ExecutionLeaf {
    pub state: Value,
    pub depth: u64,
    pub reason: String,
    /// Legacy human-readable diagnostic context.
    ///
    /// This field is not a stable semantic encoding. Consumers must branch on `reason` and use
    /// `branch` / `observations` when they need structured transition evidence.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub detail: Option<String>,
    pub trace: Vec<TraceEntry>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub branch: Vec<TransitionIdOutput>,
    #[serde(skip_serializing_if = "Vec::is_empty")]
    pub observations: Vec<ObservationEventOutput>,
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
    pub state: Value,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
}

#[derive(Clone, Debug, Deserialize)]
#[serde(deny_unknown_fields, rename_all = "camelCase")]
pub struct ImplicationRequest {
    pub antecedent: Value,
    pub consequent: Value,
    #[serde(default)]
    pub module_name: Option<String>,
    #[serde(default = "default_backend_schema_version")]
    pub schema_version: u32,
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
pub struct ProofResultOutput {
    pub claim: String,
    pub status: String,
    pub explored_states: u64,
    pub unexplored_states: u64,
    pub leaves: Vec<ProofLeafOutput>,
}

#[derive(Clone, Debug, Serialize)]
#[serde(rename_all = "camelCase")]
pub struct ProofLeafOutput {
    pub state: Value,
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

/// A persistent backend session over one compiled KORE definition.
pub struct Backend {
    session: BackendSession,
    options: BackendOptions,
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
            #[cfg(feature = "z3-inference")]
            solvers: Default::default(),
            #[cfg(feature = "z3-inference")]
            smt_prelude: _smt_prelude,
        };
        backend.with_solver(None, |_, _| Ok(()))?;
        Ok(backend)
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
        for axiom in &definition.classified_axioms {
            *identity_counts
                .entry(&axiom.attributes().unique_id)
                .or_default() += 1;
        }
        Ok(definition
            .classified_axioms
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

    pub fn execute(&mut self, request: ExecuteRequest) -> Result<ExecutionResult, BackendError> {
        self.execute_using(request, None)
    }

    pub fn execute_observed(
        &mut self,
        request: ObservedRequest<ExecuteRequest>,
    ) -> Result<ExecutionResult, BackendError> {
        self.execute_using(request.request, Some(request.rules))
    }

    fn execute_using(
        &mut self,
        request: ExecuteRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<ExecutionResult, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        #[cfg(target_arch = "wasm32")]
        if request.step_timeout_ms.is_some() || request.moving_average_timeout {
            return Err(BackendError(
                "step timeouts require a host monotonic clock and are unavailable in this WebAssembly build"
                    .into(),
            ));
        }
        let syntax = decode_pattern(request.state)?;
        self.with_solver(request.module_name.as_deref(), |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .internalize_pattern(&syntax, &[])
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

    pub fn search(&mut self, request: SearchRequest) -> Result<SearchResponse, BackendError> {
        self.search_using(request, None)
    }

    pub fn search_observed(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<SearchResponse, BackendError> {
        self.search_using(request.request, Some(request.rules))
    }

    fn search_using(
        &mut self,
        request: SearchRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<SearchResponse, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let options = search_options(&request);
        let syntax = decode_pattern(request.state)?;
        self.with_solver(request.module_name.as_deref(), |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .internalize_pattern(&syntax, &[])
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

    pub fn search_paths(
        &mut self,
        request: SearchRequest,
    ) -> Result<PathSearchResponse, BackendError> {
        self.search_paths_using(request, None)
    }

    pub fn search_paths_observed(
        &mut self,
        request: ObservedRequest<SearchRequest>,
    ) -> Result<PathSearchResponse, BackendError> {
        self.search_paths_using(request.request, Some(request.rules))
    }

    fn search_paths_using(
        &mut self,
        request: SearchRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PathSearchResponse, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let options = search_options(&request);
        let syntax = decode_pattern(request.state)?;
        self.with_solver(request.module_name.as_deref(), |definition, solver| {
            definition
                .validate_executable_pattern(&syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .internalize_pattern(&syntax, &[])
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

    pub fn search_pattern(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<PatternSearchResponse, BackendError> {
        self.search_pattern_using(request, None)
    }

    pub fn search_pattern_observed(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<PatternSearchResponse, BackendError> {
        self.search_pattern_using(request.request, Some(request.rules))
    }

    fn search_pattern_using(
        &mut self,
        request: SearchPatternRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PatternSearchResponse, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let options = pattern_search_options(&request);
        let initial_syntax = decode_pattern(request.state)?;
        let target_syntax = decode_pattern(request.pattern)?;
        self.with_solver(request.module_name.as_deref(), |definition, solver| {
            definition
                .validate_executable_pattern(&initial_syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .internalize_pattern(&initial_syntax, &[])
                .map_err(error("could not internalize pattern-search state"))?;
            let target = definition
                .internalize_pattern(&target_syntax, &[])
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

    pub fn search_pattern_paths(
        &mut self,
        request: SearchPatternRequest,
    ) -> Result<PathPatternSearchResponse, BackendError> {
        self.search_pattern_paths_using(request, None)
    }

    pub fn search_pattern_paths_observed(
        &mut self,
        request: ObservedRequest<SearchPatternRequest>,
    ) -> Result<PathPatternSearchResponse, BackendError> {
        self.search_pattern_paths_using(request.request, Some(request.rules))
    }

    fn search_pattern_paths_using(
        &mut self,
        request: SearchPatternRequest,
        observation_rules: Option<Option<Vec<String>>>,
    ) -> Result<PathPatternSearchResponse, BackendError> {
        request.validate_schema()?;
        let schema_version = request.schema_version;
        let options = pattern_search_options(&request);
        let initial_syntax = decode_pattern(request.state)?;
        let target_syntax = decode_pattern(request.pattern)?;
        self.with_solver(request.module_name.as_deref(), |definition, solver| {
            definition
                .validate_executable_pattern(&initial_syntax)
                .map_err(error("invalid executable state"))?;
            let initial = definition
                .internalize_pattern(&initial_syntax, &[])
                .map_err(error("could not internalize path-pattern-search state"))?;
            let target = definition
                .internalize_pattern(&target_syntax, &[])
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

    pub fn simplify(&mut self, request: PatternRequest) -> Result<Value, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        let syntax = decode_pattern(request.state)?;
        let output = self.simplify_kore(request.module_name.as_deref(), &syntax)?;
        encode_pattern(&output)
    }

    pub fn implies(
        &mut self,
        request: ImplicationRequest,
    ) -> Result<ImplicationResult, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        let antecedent = decode_pattern(request.antecedent)?;
        let consequent = decode_pattern(request.consequent)?;
        let (result, result_sort) =
            self.implies_kore(request.module_name.as_deref(), &antecedent, &consequent)?;
        Ok(ImplicationResult {
            schema_version: IMPLICATION_SCHEMA_VERSION,
            status: match result.status {
                ImplicationStatus::Valid => "valid",
                ImplicationStatus::Invalid => "invalid",
                ImplicationStatus::Indeterminate => "unknown",
            }
            .into(),
            condition: result
                .condition
                .as_ref()
                .map(|condition| condition_pattern(condition, &result_sort))
                .transpose()?,
            failure: result.failure.map(|failure| format!("{failure:?}")),
        })
    }

    pub fn get_model(
        &mut self,
        request: PatternRequest,
    ) -> Result<ModelResultOutput, BackendError> {
        validate_backend_schema_version(request.schema_version)?;
        #[cfg(not(feature = "z3-inference"))]
        {
            let _ = request;
            Err(BackendError(
                "model generation requires an SMT-enabled native build; this WebAssembly build has no Z3".into(),
            ))
        }
        #[cfg(feature = "z3-inference")]
        {
            let syntax = decode_pattern(request.state)?;
            let (result, result_sort) = self.model_for(request.module_name.as_deref(), &syntax)?;
            match result {
                ModelResult::Sat(substitution) => Ok(ModelResultOutput {
                    satisfiable: "sat".into(),
                    substitution: result_sort
                        .as_ref()
                        .and_then(|sort| model_substitution(&substitution, sort))
                        .as_ref()
                        .map(encode_pattern)
                        .transpose()?,
                    reason: None,
                }),
                ModelResult::Unsat => Ok(ModelResultOutput {
                    satisfiable: "unsat".into(),
                    substitution: None,
                    reason: None,
                }),
                ModelResult::Unknown(reason) => Ok(ModelResultOutput {
                    satisfiable: "unknown".into(),
                    substitution: None,
                    reason: Some(if result_sort.is_none() {
                        "the pattern contains no model predicate".into()
                    } else {
                        reason
                    }),
                }),
            }
        }
    }

    pub fn prove(&mut self, request: ProveRequest) -> Result<ProofResultOutput, BackendError> {
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
                    if seen.insert(candidate.attributes.unique_id.clone()) {
                        circularities.push(candidate);
                    }
                }
                circularities
            } else {
                definition
                    .reachability_claims
                    .iter()
                    .filter(|candidate| {
                        (std::ptr::eq(*candidate, claim) || candidate.attributes.trusted)
                            && seen.insert(candidate.attributes.unique_id.clone())
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
                            state: encode_pattern(&externalize::constrained_pattern(
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

    pub fn with_solver<T, E>(
        &mut self,
        module: Option<&str>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError>,
    {
        let definition = self
            .session
            .definition(module)
            .map_err(error("could not select backend module"))
            .map_err(E::from)?;
        self.run_with_solver(definition, operation)
    }

    #[cfg(feature = "z3-inference")]
    fn run_with_solver<T, E>(
        &mut self,
        definition: Arc<BackendDefinition>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError>,
    {
        let module = definition.main_module.to_string();
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
        operation(
            &definition,
            self.solvers.get(&module).expect("solver was inserted"),
        )
    }

    #[cfg(not(feature = "z3-inference"))]
    fn run_with_solver<T, E>(
        &mut self,
        definition: Arc<BackendDefinition>,
        operation: impl FnOnce(&BackendDefinition, &dyn SmtSolver) -> Result<T, E>,
    ) -> Result<T, E>
    where
        E: From<BackendError>,
    {
        let _ = self.options;
        operation(&definition, &NoSolver)
    }
}

fn search_options(request: &SearchRequest) -> SearchOptions {
    SearchOptions {
        search_type: match request.search_type {
            SearchTypeArg::Final => SearchType::Final,
            SearchTypeArg::All => SearchType::Star,
            SearchTypeArg::OneStep => SearchType::One,
            SearchTypeArg::OneOrMoreSteps => SearchType::Plus,
        },
        max_depth: request.max_depth.unwrap_or(u64::MAX),
        max_breadth: request.max_breadth,
        max_results: request.max_results,
        max_simplification_iterations: request.max_simplification_iterations,
    }
}

fn default_backend_schema_version() -> u32 {
    BACKEND_SCHEMA_VERSION
}

fn validate_backend_schema_version(schema_version: u32) -> Result<(), BackendError> {
    wire::validate_schema_version(schema_version)
}

fn pattern_search_options(request: &SearchPatternRequest) -> SearchOptions {
    search_options(&SearchRequest {
        state: Value::Null,
        module_name: None,
        search_type: request.search_type,
        max_depth: request.max_depth,
        max_breadth: request.max_breadth,
        max_results: request.max_results,
        max_simplification_iterations: request.max_simplification_iterations,
        schema_version: request.schema_version,
    })
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

fn decode_pattern(value: Value) -> Result<KorePattern, BackendError> {
    kore_codec::from_value(&value).map_err(error("invalid KORE JSON"))
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

fn halt_reason(reason: &HaltReason) -> (&'static str, Option<String>) {
    match reason {
        HaltReason::Cancelled => ("cancelled", None),
        HaltReason::Stuck => ("stuck", None),
        HaltReason::Trivial { .. } => ("trivial", None),
        HaltReason::Vacuous { .. } => ("vacuous", None),
        HaltReason::Branch { .. } => ("branch", Some(format!("{reason:?}"))),
        HaltReason::CutPointRule { .. } => ("cut-point", Some(format!("{reason:?}"))),
        HaltReason::TerminalRule { .. } => ("terminal", Some(format!("{reason:?}"))),
        HaltReason::DepthBound => ("depth-bound", None),
        HaltReason::BreadthBound => ("breadth-bound", None),
        HaltReason::Indeterminate(_) => ("indeterminate", Some(format!("{reason:?}"))),
        HaltReason::Simplification(error @ SimplificationError::UnsupportedHook { .. }) => {
            ("unsupported-hook", Some(error.to_string()))
        }
        HaltReason::Simplification(_) => ("simplification-error", Some(format!("{reason:?}"))),
        HaltReason::Timeout(_) => ("timeout", Some(format!("{reason:?}"))),
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

fn error<E: fmt::Debug>(context: &'static str) -> impl FnOnce(E) -> BackendError {
    move |cause| BackendError(format!("{context}: {cause:?}"))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::kore::{parser::parse_pattern, printer::Printer};

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

    const UNSUPPORTED_HOOK_DEFINITION: &str = r#"[]
        module MAIN
            sort SortState{} [hasDomainValues{}()]
            hooked-symbol missing{}(SortState{}) : SortState{}
                [function{}(), hook{}("TEST.missing")]
        endmodule []"#;

    fn backend() -> Backend {
        Backend::new(DEFINITION, "MAIN", BackendOptions::default()).unwrap()
    }

    #[test]
    fn executable_facade_rejects_nested_macro_and_alias_states_before_internalization() {
        let alias = json("weakExistsFinally{SortS{}}(a{}())");
        let nested_macro = json(r#"\and{SortS{}}(a{}(), macroValue{}())"#);
        let assert_invalid = |error: BackendError, symbol: &str| {
            let error = error.to_string();
            assert!(error.contains("invalid executable state"), "{error}");
            assert!(error.contains(symbol), "{error}");
        };

        assert_invalid(
            backend()
                .execute(ExecuteRequest {
                    state: alias.clone(),
                    ..ExecuteRequest::default()
                })
                .unwrap_err(),
            "weakExistsFinally",
        );
        assert_invalid(
            backend()
                .search(SearchRequest {
                    state: nested_macro.clone(),
                    ..SearchRequest::default()
                })
                .unwrap_err(),
            "macroValue",
        );
        assert_invalid(
            backend()
                .search_paths(SearchRequest {
                    state: alias.clone(),
                    ..SearchRequest::default()
                })
                .unwrap_err(),
            "weakExistsFinally",
        );
        assert_invalid(
            backend()
                .search_pattern(SearchPatternRequest {
                    state: nested_macro,
                    pattern: json("a{}()"),
                    ..SearchPatternRequest::default()
                })
                .unwrap_err(),
            "macroValue",
        );
        assert_invalid(
            backend()
                .search_pattern_paths(SearchPatternRequest {
                    state: alias,
                    pattern: json("a{}()"),
                    ..SearchPatternRequest::default()
                })
                .unwrap_err(),
            "weakExistsFinally",
        );
    }

    fn json(source: &str) -> Value {
        encode_pattern(&parse_pattern(source).unwrap()).unwrap()
    }

    fn text(value: Value) -> String {
        Printer::compact().print_pattern(&decode_pattern(value).unwrap())
    }

    #[test]
    fn search_wire_types_round_trip_every_disposition() {
        let state = SearchStateOutput {
            state: json("a{}()"),
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
                state: json("a{}()"),
                schema_version: 99,
                ..ExecuteRequest::default()
            })
            .unwrap_err();
        assert!(error.to_string().contains("schema version 99"), "{error}");
    }

    #[test]
    fn facade_decodes_deep_kore_json_without_a_recursion_limit() {
        let sort = serde_json::json!({ "tag": "SortApp", "name": "SortK", "args": [] });
        let mut term = serde_json::json!({ "tag": "Top", "sort": sort });
        for _ in 0..160 {
            term = serde_json::json!({ "tag": "Not", "sort": sort, "arg": term });
        }
        let envelope = serde_json::json!({ "format": "KORE", "version": 1, "term": term });

        assert!(decode_pattern(envelope).is_ok());
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
                state: json("a{}()"),
                max_depth: Some(2),
                ..ExecuteRequest::default()
            })
            .unwrap();
        assert_eq!(execution.leaves.len(), 1);
        assert_eq!(text(execution.leaves[0].state.clone()), "c{}()");

        let implication = backend
            .implies(ImplicationRequest {
                antecedent: json("X:S"),
                consequent: json("X:S"),
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
    fn persistent_backend_follows_the_reference_implication_matrix() {
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
                    antecedent: json(antecedent),
                    consequent: json(consequent),
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
                    antecedent: json(top),
                    consequent: json(consequent),
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
                antecedent: json("a{}()"),
                consequent: json(r#"\not{SortS{}}(a{}())"#),
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
                antecedent: json("a{}()"),
                consequent: json("t{}()"),
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
                    .internalize_term(&parse_pattern("a{}()").unwrap(), &[])
                    .unwrap(),
            )]),
            witnesses: Substitution::from([(
                Variable::new("Y", sort.clone()),
                definition
                    .internalize_term(&parse_pattern("b{}()").unwrap(), &[])
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
                antecedent: json("a{}()"),
                consequent: json("a{}()"),
                module_name: None,
                schema_version: BACKEND_SCHEMA_VERSION,
            })
            .unwrap();
        let result = serde_json::to_value(result).unwrap();

        assert_eq!(result["schemaVersion"], 2, "{result:#}");
    }

    #[test]
    fn persistent_backend_names_and_structures_unsupported_hook_failures() {
        let state = json(r#"missing{}(\dv{SortState{}}("value"))"#);
        let mut backend = Backend::new(
            UNSUPPORTED_HOOK_DEFINITION,
            "MAIN",
            BackendOptions::default(),
        )
        .unwrap();

        let execution = backend
            .execute(ExecuteRequest {
                state: state.clone(),
                ..ExecuteRequest::default()
            })
            .unwrap();
        assert_eq!(execution.leaves[0].reason, "unsupported-hook");
        assert!(
            execution.leaves[0]
                .detail
                .as_deref()
                .is_some_and(|detail| detail.contains("TEST.missing")),
            "{:#?}",
            execution.leaves[0]
        );

        let search = backend
            .search(SearchRequest {
                state,
                ..SearchRequest::default()
            })
            .unwrap();
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
        let result = backend
            .search(SearchRequest {
                state: json("a{}()"),
                ..SearchRequest::default()
            })
            .unwrap();
        assert_eq!(result.schema_version, BACKEND_SCHEMA_VERSION);
        assert_eq!(result.modality, ResultModalityOutput::StateSet);
        assert_eq!(result.states.len(), 1);
        assert_eq!(text(result.states[0].state.clone()), "c{}()");
        assert!(result.incomplete.is_empty());

        let bounded = backend
            .search(SearchRequest {
                state: json("a{}()"),
                max_results: Some(0),
                ..SearchRequest::default()
            })
            .unwrap();
        assert!(bounded.states.is_empty());
        assert_eq!(bounded.incomplete, [IncompleteSearchOutput::ResultBound]);
    }

    #[test]
    fn persistent_backend_searches_deterministic_path_witnesses() {
        let request = SearchRequest {
            state: json("initial{}()"),
            ..SearchRequest::default()
        };
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
            .search_pattern(SearchPatternRequest {
                state: json("a{}()"),
                pattern: json("c{}()"),
                ..SearchPatternRequest::default()
            })
            .unwrap();
        assert_eq!(state_set.modality, ResultModalityOutput::StateSet);
        assert_eq!(state_set.matches.len(), 1);
        assert_eq!(text(state_set.matches[0].state.state.clone()), "c{}()");

        let mut diamond =
            Backend::new(DIAMOND_DEFINITION, "DIAMOND", BackendOptions::default()).unwrap();
        let path_set = diamond
            .search_pattern_paths(SearchPatternRequest {
                state: json("initial{}()"),
                pattern: json("merged{}()"),
                ..SearchPatternRequest::default()
            })
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

    #[test]
    fn observed_searches_expose_filtered_transition_streams_atomically() {
        let request = SearchRequest {
            state: json("a{}()"),
            ..SearchRequest::default()
        };
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
        assert!(error.to_string().contains("UnknownRule"), "{error}");
    }

    #[test]
    fn execute_preserves_effects_and_observed_execution_attributes_them() {
        let request = ExecuteRequest {
            state: json(r#"log{}(\dv{SortString{}}("one line"))"#),
            ..ExecuteRequest::default()
        };
        let mut backend = Backend::new(LOG_DEFINITION, "MAIN", BackendOptions::default()).unwrap();
        let ordinary = backend.execute(request.clone()).unwrap();
        assert_eq!(
            ordinary.effects,
            [EffectOutput::UserLog {
                message: "one line".into()
            }]
        );
        assert!(ordinary.leaves[0].observations.is_empty());

        let observed = backend
            .execute_observed(ObservedRequest {
                request,
                rules: None,
            })
            .unwrap();
        let [ObservationEventOutput::Transition { id, effects, .. }] =
            observed.leaves[0].observations.as_slice()
        else {
            panic!("expected one committed transition observation")
        };
        assert_eq!(id.rule, "builtin:IO.logString");
        assert_eq!(effects, &ordinary.effects);
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
            .rewrite_theory
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
            state: json(DUPLICATE_UNLABELLED_STATE),
            stop_at_branch: true,
            ..ExecuteRequest::default()
        };
        let mut outcomes = Vec::new();
        for definition in [single, duplicated] {
            let mut backend =
                Backend::from_internalized(definition, BackendOptions::default()).expect("backend");
            let result = backend.execute(request.clone()).unwrap();
            let [leaf] = result.leaves.as_slice() else {
                panic!("expected one leaf: {:?}", result.leaves);
            };
            assert_ne!(leaf.reason, "branch");
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
                leaf.reason.clone(),
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
                state: json("c{}()"),
                module_name: Some("EXTRA".into()),
                max_depth: Some(1),
                ..ExecuteRequest::default()
            })
            .unwrap();
        assert_eq!(text(execution.leaves[0].state.clone()), "a{}()");
    }

    #[cfg(not(feature = "z3-inference"))]
    #[test]
    fn portable_model_generation_reports_the_capability_boundary() {
        let error = backend()
            .get_model(PatternRequest {
                state: json("a{}()"),
                module_name: None,
                schema_version: BACKEND_SCHEMA_VERSION,
            })
            .unwrap_err();
        assert!(error.to_string().contains("no Z3"));
    }
}
