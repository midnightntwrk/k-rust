//! The KORE JSON-RPC 2.0 server: JSON framing, the FIFO of in-flight requests, fault and log vocabularies, and Booster-compatible response shaping. Every backend operation goes through `Backend`.

use std::{
    collections::{BTreeSet, VecDeque},
    error::Error,
    io::{self, BufWriter, Read, Write},
    net::{TcpListener, TcpStream, ToSocketAddrs},
    sync::{
        Arc, Mutex,
        atomic::{AtomicU8, Ordering},
        mpsc,
    },
    thread,
    time::Duration,
};

#[cfg(test)]
use k_rust::backend::BackendOptions;
use k_rust::backend::{
    Backend, BackendError, execution as backend_execution, implication as backend_implication,
    simplification as backend_simplification,
};
use k_rust::kore::{
    ast::Pattern as KorePattern, codec as kore_codec, json as kore_json, parser::parse_module,
};
use k_rust::names::WellKnownSymbol;
use k_rust_backend::{
    cancellation::{CancellationToken, cancellation_requested},
    definition::{BackendDefinition, DefinitionError, PatternOrPredicate},
    externalize,
    implication::{
        ImplicationError, ImplicationRequestError, ImplicationResult, ImplicationStatus, Side,
        special_case, validate_request,
    },
    matching::SortGraph,
    rewrite::{
        AppliedRule, ExecutionBranchMode, ExecutionMode, ExecutionOptions, HaltReason, Pattern,
        TraceKind, substitute_predicates,
    },
    rule::Predicate,
    session::SessionError,
    simplify::{DEFAULT_MAX_SIMPLIFICATION_ITERATIONS, SimplificationError, SimplificationOptions},
    smt::{ModelResult, SmtError, SmtSolver},
    substitution::{Substitution, extract_substitution, substitute},
    term::{Name as BackendName, Sort as BackendSort, Term, Variable},
};
use serde::{Deserialize, Serialize};
use serde_json::{Map, Value, json, value::RawValue};

#[cfg(test)]
use k_rust_backend::session::BackendSession;

const JSON_RPC_VERSION: &str = "2.0";
const CONNECTION_STACK_SIZE: usize = 64 * 1024 * 1024;
const REQUEST_PENDING: u8 = 0;
const REQUEST_CANCELLED: u8 = 1;
const REQUEST_COMPLETED: u8 = 2;
/// A connection's session ends when its reader stops (end of stream or a read error); its
/// requests are then cancelled. A peer that vanishes without closing (crash, lost network)
/// produces neither until the operating system gives up on it, so accepted sockets carry two
/// bounds on how long the OS keeps a silent peer:
/// - TCP keepalive, which only probes a connection with nothing in flight: after
///   `KEEPALIVE_IDLE` without traffic the OS sends a probe every `KEEPALIVE_INTERVAL`, and after
///   `KEEPALIVE_RETRIES` unanswered probes the pending read fails, at most
///   `KEEPALIVE_IDLE + KEEPALIVE_RETRIES * KEEPALIVE_INTERVAL` = 25 s after the peer's last segment.
/// - `TCP_USER_TIMEOUT` = `UNACKNOWLEDGED_DATA_TIMEOUT` (Linux and Android), which covers the case
///   keepalive skips: while response bytes sent to the peer stay unacknowledged the OS retransmits
///   instead of probing, and the connection fails once data has stayed unacknowledged for 25 s,
///   rather than when retransmission gives up (about 15 minutes with the Linux default
///   `tcp_retries2`). It also fails a live client whose receive window has stayed full for 25 s,
///   i.e. one that stopped reading a response larger than the socket buffers.
///
/// The two timers do not overlap: `TCP_USER_TIMEOUT` counts from the first transmission of the
/// oldest unacknowledged segment, and keepalive stops probing once data is in flight. On those
/// systems a silent vanished peer is therefore detected about 25 s after the later of its last
/// segment and the first transmission of a response segment it has not acknowledged. Such a
/// response can only be sent before keepalive has failed the connection, so the worst case is
/// under 50 s after the peer falls silent (a response sent 20 s after it: about 45 s). Elsewhere
/// the in-flight case waits for the OS retransmission limit.
/// A live idle client costs one empty segment each way per `KEEPALIVE_IDLE`.
const KEEPALIVE_IDLE: Duration = Duration::from_secs(10);
const KEEPALIVE_INTERVAL: Duration = Duration::from_secs(5);
const KEEPALIVE_RETRIES: u32 = 3;
#[cfg(any(target_os = "linux", target_os = "android"))]
const UNACKNOWLEDGED_DATA_TIMEOUT: Duration = Duration::from_secs(
    KEEPALIVE_IDLE.as_secs() + KEEPALIVE_RETRIES as u64 * KEEPALIVE_INTERVAL.as_secs(),
);

struct RequestControl {
    token: CancellationToken,
    state: AtomicU8,
    cancellation_response: Option<String>,
}

impl RequestControl {
    fn new(message: &str) -> Self {
        Self {
            token: CancellationToken::new(),
            state: AtomicU8::new(REQUEST_PENDING),
            cancellation_response: cancellation_response(message),
        }
    }

    fn cancel(&self) -> bool {
        if self
            .state
            .compare_exchange(
                REQUEST_PENDING,
                REQUEST_CANCELLED,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_err()
        {
            return false;
        }
        self.token.cancel();
        true
    }

    fn is_cancelled(&self) -> bool {
        self.state.load(Ordering::Acquire) == REQUEST_CANCELLED
    }

    fn complete(&self) -> bool {
        self.state
            .compare_exchange(
                REQUEST_PENDING,
                REQUEST_COMPLETED,
                Ordering::AcqRel,
                Ordering::Acquire,
            )
            .is_ok()
    }
}

pub(super) struct RpcService {
    backend: Backend,
}

#[derive(Debug)]
struct RpcFault {
    code: i64,
    message: String,
    data: Option<Value>,
}

/// `Kore.JsonRpc.Error.JsonRpcBackendError`; the discriminant is the wire code.
#[derive(Clone, Copy, Debug)]
#[repr(i64)]
#[allow(dead_code)]
enum BackendErrorKind {
    CouldNotParsePattern = 1,
    CouldNotVerifyPattern = 2,
    CouldNotFindModule = 3,
    ImplicationCheckError = 4,
    SmtSolverError = 5,
    Aborted = 6,
    MultipleStates = 7,
    InvalidModule = 8,
    DuplicateModuleName = 9,
}

impl BackendErrorKind {
    fn message(self) -> &'static str {
        match self {
            Self::CouldNotParsePattern => "Could not parse pattern",
            Self::CouldNotVerifyPattern => "Could not verify pattern",
            Self::CouldNotFindModule => "Could not find module",
            Self::ImplicationCheckError => "Implication check error",
            Self::SmtSolverError => "Smt solver error",
            Self::Aborted => "Aborted",
            Self::MultipleStates => "Multiple states",
            Self::InvalidModule => "Invalid module",
            Self::DuplicateModuleName => "Duplicate module name",
        }
    }
}

/// The shipped server's error detail object, with unavailable context omitted.
#[derive(Debug, Serialize)]
struct ErrorDetail {
    error: String,
    #[serde(skip_serializing_if = "Option::is_none")]
    context: Option<Vec<String>>,
    #[serde(skip_serializing_if = "Option::is_none")]
    term: Option<Value>,
}

impl ErrorDetail {
    fn message(error: impl Into<String>) -> Self {
        Self {
            error: error.into(),
            context: None,
            term: None,
        }
    }
}

#[derive(Debug)]
struct KoreJson(KorePattern);

impl<'de> Deserialize<'de> for KoreJson {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let raw = Box::<RawValue>::deserialize(deserializer)?;
        kore_json::from_str(raw.get())
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
struct ExecuteParams {
    state: KoreJson,
    #[serde(default)]
    max_depth: Option<u64>,
    /// k-rust extension to the upstream kore-rpc execute parameters.
    #[serde(default)]
    max_simplification_iterations: Option<usize>,
    #[serde(default)]
    module: Option<String>,
    #[serde(default)]
    cut_point_rules: Vec<String>,
    #[serde(default)]
    terminal_rules: Vec<String>,
    #[serde(default)]
    moving_average_step_timeout: bool,
    #[serde(default)]
    step_timeout: Option<u64>,
    #[serde(default)]
    assume_state_defined: bool,
    #[serde(default)]
    log_successful_rewrites: bool,
    #[serde(default)]
    log_failed_rewrites: bool,
    #[serde(default)]
    booster_only: bool,
    #[serde(default)]
    haskell_logging: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
struct SimplifyParams {
    // Standalone simplify deliberately remains unbounded for Kore fallback parity.
    state: KoreJson,
    #[serde(default)]
    module: Option<String>,
    #[serde(default)]
    booster_only: bool,
    #[serde(default)]
    haskell_logging: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
struct ImpliesParams {
    antecedent: KoreJson,
    consequent: KoreJson,
    #[serde(default)]
    module: Option<String>,
    #[serde(default)]
    assume_defined: bool,
    #[serde(default)]
    booster_only: bool,
    #[serde(default)]
    haskell_logging: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
struct AddModuleParams {
    module: String,
    #[serde(default)]
    name_as_id: bool,
    #[serde(default)]
    haskell_logging: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case", deny_unknown_fields)]
struct GetModelParams {
    state: KoreJson,
    #[serde(default)]
    module: Option<String>,
    #[serde(default)]
    booster_only: bool,
    #[serde(default)]
    haskell_logging: Vec<String>,
}

impl RpcFault {
    fn cancelled() -> Self {
        Self {
            code: -32000,
            message: "Request cancelled".into(),
            data: Some(Value::Null),
        }
    }

    fn cancel_not_supported() -> Self {
        Self {
            code: -32601,
            message: "Cancel not supported".into(),
            data: None,
        }
    }

    fn invalid_request(data: Option<Value>) -> Self {
        Self {
            code: -32600,
            message: "Invalid request".into(),
            data,
        }
    }

    fn invalid_params(data: Option<Value>) -> Self {
        Self {
            code: -32602,
            message: "Invalid params".into(),
            data,
        }
    }

    fn backend_error(kind: BackendErrorKind, data: Value) -> Self {
        Self {
            code: kind as i64,
            message: kind.message().into(),
            data: Some(data),
        }
    }

    fn verify(details: Vec<ErrorDetail>) -> Self {
        Self::backend_error(
            BackendErrorKind::CouldNotVerifyPattern,
            serde_json::to_value(details).expect("error details are serializable"),
        )
    }

    fn invalid_module(detail: ErrorDetail) -> Self {
        Self::backend_error(
            BackendErrorKind::InvalidModule,
            serde_json::to_value(detail).expect("error details are serializable"),
        )
    }

    fn aborted(error: impl Into<String>) -> Self {
        Self::backend_error(BackendErrorKind::Aborted, Value::String(error.into()))
    }

    fn runtime(error: impl Into<String>, term: Option<&Term>) -> Self {
        let mut data = Map::from_iter([("error".into(), Value::String(error.into()))]);
        if let Some(term) = term {
            let term = kore_json::to_value(&externalize::term(term)).unwrap_or_else(|error| {
                json!({ "encoding-error": format!("could not encode runtime-error term: {error}") })
            });
            data.insert("term".into(), term);
        }
        Self {
            code: -32002,
            message: "Runtime error".into(),
            data: Some(Value::Object(data)),
        }
    }

    fn is_prelude_failure(&self) -> bool {
        self.code == -32002
            && self
                .data
                .as_ref()
                .and_then(|data| data.get("error"))
                .and_then(Value::as_str)
                .is_some_and(|error| {
                    error == "could not initialize Z3: InconsistentPrelude"
                        || error.starts_with("could not initialize Z3: UnknownPrelude(")
                })
    }

    fn implication(error: impl Into<String>, context: Vec<String>) -> Self {
        let detail = ErrorDetail {
            error: error.into(),
            context: Some(context),
            term: None,
        };
        Self::backend_error(
            BackendErrorKind::ImplicationCheckError,
            serde_json::to_value(detail).expect("error details are serializable"),
        )
    }

    fn module(module: &str, _error: impl ToString) -> Self {
        Self::backend_error(
            BackendErrorKind::CouldNotFindModule,
            Value::String(module.into()),
        )
    }

    fn duplicate_module_name(module: String) -> Self {
        Self::backend_error(BackendErrorKind::DuplicateModuleName, Value::String(module))
    }

    fn into_value(self, id: Value) -> Value {
        let mut error = Map::from_iter([
            ("code".into(), Value::from(self.code)),
            ("message".into(), Value::String(self.message)),
        ]);
        if let Some(data) = self.data {
            error.insert("data".into(), data);
        }
        json!({ "jsonrpc": JSON_RPC_VERSION, "id": id, "error": error })
    }
}

impl From<BackendError> for RpcFault {
    fn from(error: BackendError) -> Self {
        Self::runtime(error.to_string(), None)
    }
}

impl RpcService {
    #[cfg(test)]
    pub(super) fn new(session: BackendSession) -> Self {
        Self {
            backend: Backend::from_session(session, BackendOptions::default(), None)
                .expect("test backend should initialize"),
        }
    }

    pub(super) fn with_backend(backend: Backend) -> Self {
        Self { backend }
    }

    fn ensure_module(&mut self, module: Option<&str>) -> Result<(), RpcFault> {
        let requested = module.unwrap_or(self.backend.default_module()).to_owned();
        self.backend
            .select_definition(module)
            .map(|_| ())
            .map_err(|error| RpcFault::module(&requested, error))
    }

    /// Handle one complete JSON-RPC message. Notifications intentionally produce no response.
    pub(super) fn handle_line(&mut self, line: &str) -> Option<String> {
        let message = match parse_json_value(line) {
            Ok(message) => message,
            Err(_) => {
                let error = RpcFault {
                    code: -32700,
                    message: "Parse error".into(),
                    data: None,
                };
                return Some(
                    serde_json::to_string(&error.into_value(Value::Null))
                        .expect("JSON-RPC errors are serializable"),
                );
            }
        };
        let response = match message {
            Value::Array(requests) if requests.is_empty() => {
                Some(RpcFault::invalid_request(Some(json!([]))).into_value(Value::Null))
            }
            Value::Array(requests) => {
                let responses = requests
                    .into_iter()
                    .filter_map(|request| self.handle_request(request))
                    .collect::<Vec<_>>();
                (!responses.is_empty()).then_some(Value::Array(responses))
            }
            request => self.handle_request(request),
        };
        response.map(|response| {
            serde_json::to_string(&response).expect("JSON-RPC responses are serializable")
        })
    }

    fn handle_request(&mut self, request: Value) -> Option<Value> {
        let Some(object) = request.as_object() else {
            return Some(RpcFault::invalid_request(Some(request)).into_value(Value::Null));
        };
        let id_present = object.contains_key("id");
        let id = object.get("id").cloned().unwrap_or(Value::Null);
        let valid_id = id.is_null() || id.is_number() || id.is_string();
        let method = object.get("method").and_then(Value::as_str);
        if object.get("jsonrpc").and_then(Value::as_str) != Some(JSON_RPC_VERSION)
            || method.is_none()
            || !valid_id
        {
            return Some(RpcFault::invalid_request(Some(request)).into_value(Value::Null));
        }
        let method = method.expect("checked above");
        let params = object.get("params").cloned().unwrap_or(Value::Null);
        let result = self.dispatch(method, params);
        if !id_present {
            return None;
        }
        Some(match result {
            Ok(result) => json!({ "jsonrpc": JSON_RPC_VERSION, "id": id, "result": result }),
            Err(error) => error.into_value(id),
        })
    }

    fn dispatch(&mut self, method: &str, params: Value) -> Result<Value, RpcFault> {
        if cancellation_requested() {
            return Err(RpcFault::cancelled());
        }
        let requested_logs = params
            .get("haskell-logging")
            .and_then(Value::as_array)
            .into_iter()
            .flatten()
            .filter_map(Value::as_str)
            .map(str::to_owned)
            .collect::<Vec<_>>();
        let result = match method {
            "execute" => self.execute(decode_params(params)?),
            "simplify" => self.simplify(decode_params(params)?),
            "implies" => self.implies(decode_params(params)?),
            "add-module" => self.add_module(decode_params(params)?),
            "get-model" => self.get_model(decode_params(params)?),
            "cancel" => Err(RpcFault::cancel_not_supported()),
            _ => Err(RpcFault {
                code: -32601,
                message: "Method not found".into(),
                data: Some(Value::String(method.into())),
            }),
        };
        if cancellation_requested()
            && !result
                .as_ref()
                .err()
                .is_some_and(RpcFault::is_prelude_failure)
        {
            Err(RpcFault::cancelled())
        } else {
            result.map(|mut result| {
                attach_legacy_log_entries(method, &requested_logs, &mut result);
                result
            })
        }
    }

    fn execute(&mut self, params: ExecuteParams) -> Result<Value, RpcFault> {
        let ExecuteParams {
            state,
            max_depth,
            max_simplification_iterations,
            module,
            cut_point_rules,
            terminal_rules,
            moving_average_step_timeout,
            step_timeout,
            assume_state_defined,
            log_successful_rewrites,
            log_failed_rewrites,
            booster_only,
            haskell_logging,
        } = params;
        let _booster_only = booster_only;
        self.ensure_module(module.as_deref())?;
        self.backend
            .with_solver(module.as_deref(), |definition, solver| {
                let syntax = state.0;
                definition
                    .validate_executable_pattern(&syntax)
                    .map_err(|error| pattern_fault(error, &syntax))?;
                let initial = definition
                    .internalize_pattern(&syntax, &[])
                    .map_err(|error| pattern_fault(error, &syntax))?;
                let configuration_variables = pattern_variables(&initial);
                // RPC deliberately has no execution IO state. Console hooks stay unsupported until a
                // protocol owns branch-local input and structured transcripts.
                let result = backend_execution::run(
                    definition,
                    initial,
                    ExecutionOptions {
                        max_depth: max_depth.unwrap_or(u64::MAX),
                        max_simplification_iterations: max_simplification_iterations
                            .unwrap_or(DEFAULT_MAX_SIMPLIFICATION_ITERATIONS),
                        mode: ExecutionMode::All,
                        branch_mode: ExecutionBranchMode::StopAtBranch,
                        cut_point_rules: cut_point_rules.into_iter().collect(),
                        terminal_rules: terminal_rules.into_iter().collect(),
                        step_timeout: step_timeout.map(Duration::from_millis),
                        moving_average_timeout: moving_average_step_timeout,
                        assume_initial_defined: assume_state_defined,
                        ..ExecutionOptions::default()
                    },
                    solver,
                );
                let leaf = result
                    .leaves
                    .into_iter()
                    .next()
                    .ok_or_else(|| RpcFault::runtime("execution produced no result", None))?;
                let mut output = Map::new();
                let (reason, next_states, rule) = match &leaf.halt_reason {
                    HaltReason::Cancelled => return Err(RpcFault::cancelled()),
                    HaltReason::Stuck => ("stuck", None, None),
                    HaltReason::Trivial { .. } | HaltReason::Vacuous { .. } => {
                        ("vacuous", None, None)
                    }
                    HaltReason::DepthBound => ("depth-bound", None, None),
                    HaltReason::BreadthBound => ("aborted", None, None),
                    HaltReason::Timeout(_) => ("timeout", None, None),
                    HaltReason::Simplification(
                        error @ SimplificationError::UnsupportedHook { term, .. },
                    ) => return Err(RpcFault::runtime(error.to_string(), Some(term))),
                    HaltReason::Simplification(error @ SimplificationError::StackExhausted) => {
                        return Err(stack_exhausted_fault(error));
                    }
                    HaltReason::Indeterminate(_) | HaltReason::Simplification(_) => {
                        ("aborted", None, None)
                    }
                    HaltReason::Branch {
                        branches,
                        remainder,
                    } => {
                        let mut next_states = branches
                            .iter()
                            .map(|applied| {
                                execute_applied_state(definition, applied, &configuration_variables)
                            })
                            .collect::<Result<Vec<_>, _>>()?;
                        if let Some(remainder) = remainder {
                            next_states.push(execute_state(
                                definition,
                                &remainder.pattern,
                                &configuration_variables,
                            )?);
                        }
                        ("branching", Some(next_states), None)
                    }
                    HaltReason::CutPointRule { rule, next_states } => (
                        "cut-point-rule",
                        Some(
                            next_states
                                .iter()
                                .map(|applied| {
                                    execute_state(
                                        definition,
                                        &applied.pattern,
                                        &configuration_variables,
                                    )
                                })
                                .collect::<Result<Vec<_>, _>>()?,
                        ),
                        Some(rule.clone()),
                    ),
                    HaltReason::TerminalRule { rule } => {
                        ("terminal-rule", None, Some(rule.clone()))
                    }
                };
                output.insert("reason".into(), Value::String(reason.into()));
                output.insert("depth".into(), Value::from(leaf.depth));
                if let Some(rule) = rule {
                    output.insert("rule".into(), Value::String(rule));
                }
                output.insert(
                    "state".into(),
                    execute_state(definition, &leaf.pattern, &configuration_variables)?,
                );
                if let Some(next_states) = next_states {
                    output.insert("next-states".into(), Value::Array(next_states));
                }
                if log_successful_rewrites || log_failed_rewrites {
                    let mut logs = leaf
                        .trace
                        .iter()
                        .filter(|entry| entry.kind == TraceKind::Rewrite)
                        .map(|entry| {
                            json!({
                                "tag": "rewrite",
                                "origin": "booster",
                                "result": {
                                    "tag": "success",
                                    "rule-id": entry.unique_id,
                                },
                            })
                        })
                        .collect::<Vec<_>>();
                    if log_failed_rewrites {
                        logs.extend(execute_failed_rewrite_logs(&leaf.halt_reason));
                    }
                    if !logs.is_empty() {
                        output.insert("logs".into(), Value::Array(logs));
                    }
                }
                if !haskell_logging.is_empty() {
                    output.insert(
                        "haskell-log-entries".into(),
                        Value::Array(legacy_execution_log_entries(
                            &haskell_logging,
                            &leaf.trace,
                            &leaf.halt_reason,
                        )),
                    );
                }
                Ok(Value::Object(output))
            })
    }

    fn simplify(&mut self, params: SimplifyParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        let _haskell_logging = params.haskell_logging;
        self.ensure_module(params.module.as_deref())?;
        let syntax = params.state.0;
        self.backend.with_solver(
            params.module.as_deref(),
            |definition, solver| match definition
                .internalize_pattern_or_predicate(&syntax, &[])
                .map_err(|error| pattern_fault(error, &syntax))?
            {
                PatternOrPredicate::Term(pattern) => {
                    let simplified = backend_simplification::simplify_pattern(
                        definition,
                        &pattern,
                        SimplificationOptions::unbounded(),
                        solver,
                    )
                    .map_err(|error| simplify_fault(error, &pattern.term.sort()))?;
                    Ok(json!({
                        "state": encode_kore(&externalize::constrained_pattern(&simplified))?
                    }))
                }
                PatternOrPredicate::Predicate(predicate, result_sort) => {
                    let simplified = backend_simplification::simplify_predicate(
                        definition,
                        &predicate,
                        SimplificationOptions::unbounded(),
                        solver,
                    )
                    .map_err(|error| simplify_fault(error, &result_sort))?;
                    Ok(json!({
                        "state": encode_kore(&externalize::ml_pattern(&simplified, &result_sort))?
                    }))
                }
            },
        )
    }

    fn add_module(&mut self, params: AddModuleParams) -> Result<Value, RpcFault> {
        let _haskell_logging = params.haskell_logging;
        let module = parse_module(&params.module)
            .map_err(|error| RpcFault::invalid_module(ErrorDetail::message(error.to_string())))?;
        let error_module = module.clone();
        let id = self
            .backend
            .add_parsed_module(&params.module, module, params.name_as_id)
            .map_err(|error| match error {
                SessionError::Definition(DefinitionError::NoSuchModule(module)) => {
                    RpcFault::invalid_module(ErrorDetail::message(format!(
                        "Module {module} not found."
                    )))
                }
                SessionError::DuplicateModuleName(module) => {
                    RpcFault::duplicate_module_name(module)
                }
                SessionError::IntroducesSorts(sorts) => {
                    RpcFault::invalid_module(ErrorDetail::message(format!(
                        "Module introduces new sorts: {}",
                        sorts.join(", ")
                    )))
                }
                SessionError::IntroducesSymbols(symbols) => {
                    RpcFault::invalid_module(ErrorDetail::message(format!(
                        "Module introduces new symbols: {}",
                        symbols.join(", ")
                    )))
                }
                SessionError::Definition(error) => {
                    RpcFault::invalid_module(module_verification_detail(&error, &error_module))
                }
            })?;
        Ok(json!({ "module": id }))
    }

    fn get_model(&mut self, params: GetModelParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        let _haskell_logging = params.haskell_logging;
        self.ensure_module(params.module.as_deref())?;
        let syntax = params.state.0;
        self.backend
            .with_solver(params.module.as_deref(), |definition, solver| {
                let Some((predicate, result_sort)) = definition
                    .internalize_model_predicate(&syntax, &[])
                    .map_err(|error| pattern_fault(error, &syntax))?
                else {
                    return Ok(json!({ "satisfiable": "Unknown" }));
                };
                match backend_simplification::model_predicate_with_solver(
                    definition, &predicate, solver,
                )
                .map_err(|error| RpcFault::runtime(error.to_string(), None))?
                {
                    ModelResult::Sat(substitution) => {
                        let mut result = json!({ "satisfiable": "Sat" });
                        if let Some(substitution) =
                            backend_simplification::model_substitution(&substitution, &result_sort)
                        {
                            result["substitution"] = encode_kore(&substitution)?;
                        }
                        Ok(result)
                    }
                    ModelResult::Unsat => Ok(json!({ "satisfiable": "Unsat" })),
                    ModelResult::Unknown(_) => Ok(json!({ "satisfiable": "Unknown" })),
                }
            })
    }

    fn implies(&mut self, params: ImpliesParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        // The reference proxy uses `assume-defined` as a backend-routing hint. The unified Rust
        // backend already runs the in-process implication path it selects.
        let _assume_defined = params.assume_defined;
        let _haskell_logging = params.haskell_logging;
        self.ensure_module(params.module.as_deref())?;
        let antecedent = params.antecedent.0;
        let consequent = params.consequent.0;
        self.backend
            .with_solver(params.module.as_deref(), |definition, solver| {
        if let Err(request_error) = validate_request(definition, &antecedent, &consequent) {
            return Err(match request_error {
                ImplicationRequestError::MacroOrAlias { side, name } => {
                    let pattern = match side {
                        Side::Antecedent => &antecedent,
                        Side::Consequent => &consequent,
                    };
                    implication_pattern_fault(
                        DefinitionError::MacroOrAliasInImplication(name),
                        pattern,
                    )
                }
                ImplicationRequestError::NonFunctionLikeAntecedent => RpcFault::implication(
                    "The check implication step expects the antecedent term to be function-like.",
                    vec![antecedent.strip_exists().to_string()],
                ),
                ImplicationRequestError::NonSingletonConsequent => RpcFault::implication(
                    "Term does not simplify to a singleton pattern",
                    vec![format!("RHS: {}", consequent.strip_exists())],
                ),
                ImplicationRequestError::ExistentialCapture {
                    captured,
                    existentials,
                } => {
                    let consequent_body = consequent.strip_exists();
                    RpcFault::implication(
                        format!(
                            "Existentials capture free variables of the antecedent: {}",
                            captured.join(", ")
                        ),
                        implication_pattern_context(&antecedent, consequent_body, &existentials),
                    )
                }
                ImplicationRequestError::SortMismatch {
                    antecedent,
                    consequent,
                } => RpcFault::implication(
                    "Antecedent and consequent must have the same sort.",
                    vec![
                        format!("LHS sort: {antecedent}"),
                        format!("RHS sort: {consequent}"),
                    ],
                ),
            });
        }
        let sort_variables = antecedent
            .sort_variables()
            .into_iter()
            .chain(consequent.sort_variables())
            .collect::<BTreeSet<_>>()
            .into_iter()
            .map(BackendName::from)
            .collect::<Vec<_>>();
        let mut special_result = special_case(&antecedent, &consequent);
        if matches!(antecedent.strip_exists(), KorePattern::Bottom { .. })
            && let Some(result) = special_result.take()
        {
            let (_, result_sort) = definition
                .internalize_predicate(&antecedent, &sort_variables)
                .map_err(|error| pattern_fault(error, &antecedent))?;
            let consequent = if matches!(
                consequent.strip_exists(),
                KorePattern::Top { .. } | KorePattern::Bottom { .. }
            ) {
                consequent
            } else {
                let (consequent_pattern, _) = definition
                    .internalize_implication_pattern(&consequent, &sort_variables)
                    .map_err(|error| pattern_fault(error, &consequent))?;
                simplified_implication_response_syntax(
                    definition,
                    &consequent,
                    &consequent_pattern,
                    solver,
                )?
            };
            return implication_result(&antecedent, &consequent, &result_sort, result);
        }
        let (antecedent_pattern, antecedent_existentials) = definition
            .internalize_implication_pattern(&antecedent, &sort_variables)
            .map_err(|error| pattern_fault(error, &antecedent))?;
        let result_sort = antecedent_pattern.term.sort();
        if matches!(consequent.strip_exists(), KorePattern::Not { .. }) {
            let result = special_result
                .take()
                .expect("not consequents are a shared implication special case");
            let antecedent = simplified_implication_response_syntax(
                definition,
                &antecedent,
                &antecedent_pattern,
                solver,
            )?;
            let consequent = simplified_not_consequent_response_syntax(
                definition,
                &consequent,
                &sort_variables,
                solver,
            )?;
            return implication_result(&antecedent, &consequent, &result_sort, result);
        }
        if let Some(result) = special_result {
            let antecedent = simplified_implication_response_syntax(
                definition,
                &antecedent,
                &antecedent_pattern,
                solver,
            )?;
            return implication_result(&antecedent, &consequent, &result_sort, result);
        }
        let (consequent_pattern, consequent_existentials) = definition
            .internalize_implication_pattern(&consequent, &sort_variables)
            .map_err(|error| pattern_fault(error, &consequent))?;
        if result_sort != consequent_pattern.term.sort() {
            return Err(RpcFault::verify(vec![ErrorDetail::message(
                "antecedent and consequent sorts differ",
            )]));
        }
        let result = backend_implication::check(
            definition,
            &antecedent_pattern,
            &antecedent_existentials,
            &consequent_pattern,
            &consequent_existentials,
            solver,
        )
        .map_err(implication_backend_fault)?;
        let vacuous_antecedent = result.status == ImplicationStatus::Valid
            && result.condition.as_ref().is_some_and(|condition| {
                condition.predicates.as_slice() == [Predicate::False]
                    && condition.substitution.is_empty()
            });
        let (antecedent, consequent) = if vacuous_antecedent {
            (antecedent, consequent)
        } else {
            (
                simplified_implication_response_syntax(
                    definition,
                    &antecedent,
                    &antecedent_pattern,
                    solver,
                )?,
                simplified_implication_response_syntax(
                    definition,
                    &consequent,
                    &consequent_pattern,
                    solver,
                )?,
            )
        };
        implication_result(&antecedent, &consequent, &result_sort, result)
            })
    }
}

/// The request ran out of the native stack of the thread serving it. The error ends this request
/// only: the thread unwound to the request's entry, so the connection keeps serving.
fn stack_exhausted_fault(error: &SimplificationError) -> RpcFault {
    RpcFault::runtime(error.to_string(), None)
}

fn simplify_fault(error: SimplificationError, result_sort: &BackendSort) -> RpcFault {
    if let SimplificationError::UnsupportedHook { term, .. } = &error {
        return RpcFault::runtime(error.to_string(), Some(term));
    }
    if let SimplificationError::StackExhausted = &error {
        return stack_exhausted_fault(&error);
    }
    let SimplificationError::SmtPredicate { predicate, error } = error else {
        return RpcFault::aborted(error.to_string());
    };
    let term = externalize::ml_pattern(&predicate, result_sort);
    let reason = match error {
        SmtError::Unknown(reason)
            if reason == "timeout" && contains_integer_power_application(&term) =>
        {
            "(incomplete (theory arithmetic))".into()
        }
        SmtError::Unknown(reason) => reason,
        error => format!("{error:?}"),
    };
    let Ok(term) = encode_kore(&term) else {
        return RpcFault::runtime("could not encode the predicate rejected by SMT", None);
    };
    RpcFault::backend_error(
        BackendErrorKind::SmtSolverError,
        json!({ "term": term, "error": reason }),
    )
}

fn contains_integer_power_application(pattern: &KorePattern) -> bool {
    pattern
        .find_application(|symbol, _| symbol.name == "Lbl'UndsXor-'Int'Unds'")
        .is_some()
}

fn implication_pattern_fault(error: DefinitionError, pattern: &KorePattern) -> RpcFault {
    let DefinitionError::MacroOrAliasInImplication(name) = &error else {
        return pattern_fault(error, pattern);
    };
    RpcFault::verify(vec![ErrorDetail {
        error: "A symbol cannot be an alias or a macro".into(),
        context: Some(vec![format!("symbol or alias '{name}'")]),
        term: None,
    }])
}

fn pattern_fault(error: DefinitionError, pattern: &KorePattern) -> RpcFault {
    RpcFault::verify(vec![verification_detail(&error, pattern)])
}

fn verification_detail(error: &DefinitionError, pattern: &KorePattern) -> ErrorDetail {
    let (message, term) = match error {
        DefinitionError::UnknownSymbol(symbol) => (
            format!("Unknown symbol '{symbol}'"),
            locate_application(pattern, symbol, None, None, None).map(|(term, _)| term),
        ),
        DefinitionError::WrongSymbolArity {
            symbol,
            expected,
            actual,
        } => (
            format!(
                "Inconsistent pattern. Symbol '{symbol}' expected {expected} arguments but got {actual}"
            ),
            locate_application(pattern, symbol, Some(*actual), None, None).map(|(term, _)| term),
        ),
        DefinitionError::IncorrectArgumentSort {
            symbol,
            index,
            expected,
            actual,
        } => {
            let actual_sort = externalize::sort(actual).to_string();
            let term = locate_application(
                pattern,
                symbol,
                None,
                Some((*index, actual_sort.as_str())),
                None,
            )
            .and_then(|(_, arguments)| arguments.get(*index));
            (
                format!(
                    "Incorrect sort: expected {} but got {actual_sort}",
                    externalize::sort(expected)
                ),
                term,
            )
        }
        DefinitionError::NotSubsort { source, target } => {
            let source = externalize::sort(source).to_string();
            let target = externalize::sort(target).to_string();
            (
                format!("{source} is not a subsort of {target}"),
                locate_application(
                    pattern,
                    WellKnownSymbol::Inj.as_str(),
                    Some(1),
                    None,
                    Some((source.as_str(), target.as_str())),
                )
                .map(|(term, _)| term),
            )
        }
        DefinitionError::ExpectedTerm(_) => ("Pattern not supported".into(), Some(pattern)),
        _ => (error.to_string(), None),
    };
    ErrorDetail {
        error: message,
        context: None,
        term: term.and_then(|term| encode_kore(term).ok()),
    }
}

fn module_verification_detail(
    error: &DefinitionError,
    module: &k_rust::kore::ast::Module,
) -> ErrorDetail {
    let pattern = module.sentences.iter().find_map(|sentence| match sentence {
        k_rust::kore::ast::Sentence::AliasDeclaration { right, .. }
        | k_rust::kore::ast::Sentence::Axiom { pattern: right, .. }
        | k_rust::kore::ast::Sentence::Claim { pattern: right, .. } => Some(right.as_ref()),
        _ => None,
    });
    match (error, pattern) {
        (DefinitionError::Verification(verification), Some(pattern))
            if verification
                .message
                .strip_prefix("Head '")
                .and_then(|message| message.strip_suffix("' not defined."))
                .is_some() =>
        {
            let symbol = verification
                .message
                .strip_prefix("Head '")
                .and_then(|message| message.strip_suffix("' not defined."))
                .expect("guarded above");
            ErrorDetail {
                error: format!("Unknown symbol '{symbol}'"),
                context: None,
                term: locate_application(pattern, symbol, None, None, None)
                    .and_then(|(term, _)| encode_kore(term).ok()),
            }
        }
        (_, Some(pattern)) => verification_detail(error, pattern),
        (_, None) => ErrorDetail::message(error.to_string()),
    }
}

fn locate_application<'a>(
    pattern: &'a KorePattern,
    symbol_name: &str,
    actual_arity: Option<usize>,
    argument_sort: Option<(usize, &str)>,
    sort_parameters: Option<(&str, &str)>,
) -> Option<(&'a KorePattern, &'a [KorePattern])> {
    let pattern = pattern.find_application(|symbol, arguments| {
        if symbol.name != symbol_name || actual_arity.is_some_and(|arity| arguments.len() != arity)
        {
            return false;
        }
        if let Some((source, target)) = sort_parameters
            && !matches!(
                symbol.sort_parameters.as_slice(),
                [actual_source, actual_target]
                    if actual_source.to_string() == source && actual_target.to_string() == target
            )
        {
            return false;
        }
        if let Some((index, expected_sort)) = argument_sort
            && arguments
                .get(index)
                .and_then(KorePattern::syntactic_sort)
                .is_some_and(|sort| sort.to_string() != expected_sort)
        {
            return false;
        }
        true
    })?;
    let KorePattern::Application { arguments, .. } = pattern else {
        unreachable!("find_application only returns application patterns");
    };
    Some((pattern, arguments))
}

fn normalized_implication_syntax(original: &KorePattern, pattern: &Pattern) -> KorePattern {
    /// Term leaves are the non-predicate conjuncts of the request pattern; they are kept in
    /// the caller's syntax while the predicate conjuncts are replaced by the simplified
    /// constraints.
    fn is_term_leaf(pattern: &KorePattern) -> bool {
        matches!(
            pattern,
            KorePattern::Application { .. }
                | KorePattern::AssociativeApplication { .. }
                | KorePattern::Variable(_)
                | KorePattern::DomainValue { .. }
                | KorePattern::String(_)
        )
    }

    fn take_term_leaves(pattern: &KorePattern) -> Option<KorePattern> {
        match pattern {
            KorePattern::And { sort, arguments } => {
                let mut arguments = arguments
                    .iter()
                    .filter_map(take_term_leaves)
                    .collect::<Vec<_>>();
                match arguments.len() {
                    0 => None,
                    1 => arguments.pop(),
                    _ => Some(KorePattern::And {
                        sort: sort.clone(),
                        arguments,
                    }),
                }
            }
            _ if is_term_leaf(pattern) => Some(pattern.clone()),
            _ => None,
        }
    }

    fn normalize_body(original: &KorePattern, pattern: &Pattern) -> KorePattern {
        let result_sort = pattern.term.sort();
        let Some(term) = take_term_leaves(original) else {
            return externalize::constrained_pattern(pattern);
        };
        let mut constraints = pattern.constraints.iter().collect::<Vec<_>>();
        constraints.sort();
        let constraints = constraints
            .into_iter()
            .map(|predicate| externalize::predicate_pattern(predicate, &result_sort))
            .collect::<Vec<_>>();
        if constraints.is_empty() {
            return term;
        }
        let sort = externalize::sort(&result_sort);
        let predicate =
            externalize::conjunction(&sort, constraints, externalize::ConjunctionShape::Balanced)
                .expect("the empty constraint case returned above");
        KorePattern::And {
            sort,
            arguments: vec![term, predicate],
        }
    }

    match original {
        KorePattern::Exists {
            sort,
            variable,
            body,
        } => KorePattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: Box::new(normalized_implication_syntax(body, pattern)),
        },
        _ => normalize_body(original, pattern),
    }
}

fn simplified_implication_response_syntax(
    definition: &BackendDefinition,
    original: &KorePattern,
    unsimplified: &Pattern,
    solver: &dyn SmtSolver,
) -> Result<KorePattern, RpcFault> {
    // The verdict is already decided; rendering runs the same simplifier the `simplify`
    // method exposes, so its failures are reported through the same fault instead of
    // echoing an unsimplified pattern next to a verdict that was computed from the
    // simplified one.
    let simplified = backend_simplification::simplify_pattern(
        definition,
        unsimplified,
        SimplificationOptions::default(),
        solver,
    )
    .map_err(|error| simplify_fault(error, &unsimplified.term.sort()))?;
    if unsimplified.term == simplified.term {
        return Ok(normalized_implication_syntax(original, &simplified));
    }

    let mut result = externalize::constrained_pattern(&simplified);
    let mut binders = Vec::new();
    let mut body = original;
    while let KorePattern::Exists {
        sort,
        variable,
        body: next,
    } = body
    {
        binders.push((sort.clone(), variable.clone()));
        body = next;
    }
    for (sort, variable) in binders.into_iter().rev() {
        result = KorePattern::Exists {
            sort,
            variable,
            body: Box::new(result),
        };
    }
    Ok(result)
}

fn simplified_not_consequent_response_syntax(
    definition: &BackendDefinition,
    original: &KorePattern,
    sort_variables: &[BackendName],
    solver: &dyn SmtSolver,
) -> Result<KorePattern, RpcFault> {
    Ok(match original {
        KorePattern::Exists {
            sort,
            variable,
            body,
        } => KorePattern::Exists {
            sort: sort.clone(),
            variable: variable.clone(),
            body: Box::new(simplified_not_consequent_response_syntax(
                definition,
                body,
                sort_variables,
                solver,
            )?),
        },
        KorePattern::Not { sort, argument } => {
            let (pattern, _) = definition
                .internalize_implication_pattern(argument, sort_variables)
                .map_err(|error| pattern_fault(error, argument))?;
            KorePattern::Not {
                sort: sort.clone(),
                argument: Box::new(simplified_implication_response_syntax(
                    definition, argument, &pattern, solver,
                )?),
            }
        }
        _ => original.clone(),
    })
}

fn implication_backend_fault(error: ImplicationError) -> RpcFault {
    RpcFault::backend_error(
        BackendErrorKind::ImplicationCheckError,
        serde_json::to_value(ErrorDetail::message(format!(
            "implication check failed: {error}"
        )))
        .expect("error details are serializable"),
    )
}

fn implication_pattern_context(
    antecedent: &KorePattern,
    consequent: &KorePattern,
    existentials: &[String],
) -> Vec<String> {
    vec![
        format!("LHS: {}", antecedent.strip_exists()),
        format!("RHS: {consequent}"),
        format!("existentials: [{}]", existentials.join(", ")),
    ]
}

fn failed_rewrite_log(reason: &HaltReason) -> Option<Value> {
    let (reason, rule_id) = match reason {
        HaltReason::Stuck => ("No applicable rules found", None),
        HaltReason::Indeterminate(indeterminate) => match indeterminate {
            k_rust_backend::rewrite::IndeterminateReason::SurvivingMacroOrAlias { .. } => {
                ("Invalid executable macro or alias symbol", None)
            }
            k_rust_backend::rewrite::IndeterminateReason::Match { rule_id, .. } => {
                ("Uncertain about unification of rule", Some(rule_id))
            }
            k_rust_backend::rewrite::IndeterminateReason::Instantiation { rule_id, .. } => {
                ("Unable to instantiate semantic rule", Some(rule_id))
            }
            k_rust_backend::rewrite::IndeterminateReason::Requires { rule_id, .. }
            | k_rust_backend::rewrite::IndeterminateReason::Smt { rule_id, .. } => {
                ("Uncertain about a condition in rule", Some(rule_id))
            }
            k_rust_backend::rewrite::IndeterminateReason::Remainder { rule_ids, .. } => (
                "Uncertain about the remainder after applying a rule",
                rule_ids.first(),
            ),
        },
        HaltReason::Simplification(_) => ("Internal match error", None),
        _ => return None,
    };
    let mut result = Map::from_iter([
        ("tag".into(), Value::String("failure".into())),
        ("reason".into(), Value::String(reason.into())),
    ]);
    if let Some(rule_id) = rule_id {
        result.insert("rule-id".into(), Value::String(rule_id.clone()));
    }
    Some(json!({
        "tag": "rewrite",
        "origin": "booster",
        "result": result,
    }))
}

fn execute_failed_rewrite_logs(reason: &HaltReason) -> Vec<Value> {
    let Some(failure) = failed_rewrite_log(reason) else {
        return Vec::new();
    };
    // Booster first attempts the unsimplified term, then simplifies and retries a stuck or
    // indeterminate match. The Rust executor simplifies before its attempt, so reproduce the two
    // externally observable failures here without repeating the backend work.
    if matches!(
        reason,
        HaltReason::Stuck
            | HaltReason::Indeterminate(k_rust_backend::rewrite::IndeterminateReason::Match { .. })
    ) {
        vec![failure.clone(), failure]
    } else {
        vec![failure]
    }
}

fn attach_legacy_log_entries(method: &str, requested: &[String], result: &mut Value) {
    if requested.is_empty() {
        return;
    }
    let Some(result) = result.as_object_mut() else {
        return;
    };
    let (method_name, method_context) = match method {
        "execute" => ("Execute", "execute"),
        "simplify" => ("Simplify", "simplify"),
        "implies" => ("Implies", "implies"),
        "add-module" => ("AddModule", "add-module"),
        "get-model" => ("GetModel", "get-model"),
        _ => return,
    };
    let mut entries = Vec::new();
    if legacy_log_selected(requested, &["Proxy", method_name]) {
        entries.push(json!({
            "context": ["proxy", method_context],
            "message": if method == "execute" {
                "Starting execute request".to_owned()
            } else {
                format!("{method_context} request")
            },
        }));
    }
    if let Some(Value::Array(existing)) = result.remove("haskell-log-entries") {
        entries.extend(existing);
    }
    result.insert("haskell-log-entries".into(), Value::Array(entries));
}

fn legacy_execution_log_entries(
    requested: &[String],
    trace: &[k_rust_backend::rewrite::TraceEntry],
    halt_reason: &HaltReason,
) -> Vec<Value> {
    let mut entries = trace
        .iter()
        .filter_map(|entry| {
            let (name, context) = match entry.kind {
                TraceKind::Rewrite | TraceKind::Claim => {
                    ("Rewrite", json!({ "rewrite": entry.unique_id }))
                }
                TraceKind::Simplification => (
                    "Simplification",
                    json!({ "simplification": entry.unique_id }),
                ),
                TraceKind::Remainder => ("Remainder", Value::String("remainder".into())),
            };
            legacy_log_selected(requested, &["Booster", "Execute", name, "Success"]).then(|| {
                json!({
                    "context": ["booster", "execute", context, "success"],
                    "message": {
                        "tag": "success",
                        "rule-id": entry.unique_id,
                    },
                })
            })
        })
        .collect::<Vec<_>>();
    if let Some(failure) = failed_rewrite_log(halt_reason) {
        let indeterminate = matches!(halt_reason, HaltReason::Indeterminate(_));
        let names = if indeterminate {
            &["Booster", "Execute", "Failure", "Indeterminate", "Abort"][..]
        } else {
            &["Booster", "Execute", "Failure"][..]
        };
        if legacy_log_selected(requested, names) {
            let result = failure["result"].clone();
            let mut context = vec![json!("booster"), json!("execute")];
            if let Some(rule_id) = result.get("rule-id") {
                context.push(json!({ "rewrite": rule_id }));
            }
            context.push(json!("failure"));
            if indeterminate {
                context.push(json!("indeterminate"));
                context.push(json!("abort"));
            }
            entries.push(json!({ "context": context, "message": result }));
        }
    }
    entries
}

fn legacy_log_selected(requested: &[String], contexts: &[&str]) -> bool {
    contexts
        .iter()
        .any(|context| requested.iter().any(|requested| requested == context))
}

fn decode_params<T: for<'de> Deserialize<'de>>(params: Value) -> Result<T, RpcFault> {
    let data = (!params.is_null()).then_some(params.clone());
    serde_json::from_value(params).map_err(|_| RpcFault::invalid_params(data))
}

fn parse_json_value(source: &str) -> serde_json::Result<Value> {
    let mut deserializer = serde_json::Deserializer::from_str(source);
    deserializer.disable_recursion_limit();
    let value = Value::deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(value)
}

fn encode_kore(pattern: &KorePattern) -> Result<Value, RpcFault> {
    kore_codec::to_value(pattern)
        .map_err(|error| RpcFault::runtime(format!("could not encode KORE JSON: {error}"), None))
}

fn execute_state(
    definition: &BackendDefinition,
    pattern: &Pattern,
    configuration_variables: &BTreeSet<Variable>,
) -> Result<Value, RpcFault> {
    let mut state = Map::new();
    let (predicates, substitution) = split_constraints(
        &pattern.constraints,
        configuration_variables,
        &definition.sort_graph,
    );
    let term = substitute(&pattern.term, &substitution);
    state.insert("term".into(), encode_kore(&externalize::term(&term))?);
    let predicates = substitute_predicates(&predicates, &substitution);
    let mut ordered_predicates = predicates
        .iter()
        .filter(|predicate| !matches!(predicate, Predicate::True))
        .collect::<Vec<_>>();
    ordered_predicates.sort_by(|left, right| {
        left.free_variables()
            .cmp(&right.free_variables())
            .then_with(|| left.cmp(right))
    });
    if let Some(predicate) = externalize::conjunction(
        &externalize::sort(&pattern.term.sort()),
        ordered_predicates
            .into_iter()
            .map(|predicate| {
                externalize::booster_predicate_pattern(definition, predicate, &pattern.term.sort())
            })
            .collect(),
        externalize::ConjunctionShape::Flat,
    ) {
        state.insert("predicate".into(), encode_kore(&predicate)?);
    }
    if let Some(substitution) =
        backend_simplification::model_substitution(&substitution, &pattern.term.sort())
    {
        state.insert("substitution".into(), encode_kore(&substitution)?);
    }
    Ok(Value::Object(state))
}

fn execute_applied_state(
    definition: &BackendDefinition,
    applied: &AppliedRule,
    configuration_variables: &BTreeSet<Variable>,
) -> Result<Value, RpcFault> {
    let mut state = execute_state(definition, &applied.pattern, configuration_variables)?;
    let object = state
        .as_object_mut()
        .expect("execute_state always returns an object");
    object.insert("rule-id".into(), Value::String(applied.unique_id.clone()));
    if let Some(rule_predicate) = externalize::predicates_pattern(
        &applied.rule_predicates,
        &applied.pattern.term.sort(),
        |predicate| {
            externalize::booster_rule_predicate_pattern_in_definition(
                definition,
                predicate,
                &applied.pattern.term.sort(),
            )
        },
        externalize::ConjunctionShape::LeftNested,
    ) {
        object.insert("rule-predicate".into(), encode_kore(&rule_predicate)?);
    }
    let (_, state_substitution) = split_constraints(
        &applied.pattern.constraints,
        configuration_variables,
        &definition.sort_graph,
    );
    if let Some(substitution) = externalize_rule_substitution(
        &applied.rule_substitution,
        &state_substitution,
        &applied.pattern.term.sort(),
    ) {
        object.insert("rule-substitution".into(), encode_kore(&substitution)?);
    }
    Ok(state)
}

fn externalize_rule_substitution(
    substitution: &Substitution,
    state_substitution: &Substitution,
    result_sort: &BackendSort,
) -> Option<KorePattern> {
    // `externalize::external_variable_name` drops the `Rule#`/`Ex#` markers the way Booster's
    // externaliseRuleMarker does when the bindings are emitted below.
    let substitution = substitution
        .iter()
        .map(|(variable, value)| (variable.clone(), substitute(value, state_substitution)))
        .collect();
    // The response carries the bindings as one left-nested `\and` at the conjunction's sort.
    // Whether there is a conjunct to re-nest is decided on a borrow first, so that the
    // conjuncts can then be moved out of the conjunction instead of copied next to it; a
    // non-conjunction, or a conjunction whose operands are all its unit, is returned as built.
    backend_simplification::model_substitution(&substitution, result_sort).map(|pattern| {
        let sort = match &pattern {
            KorePattern::And { sort, .. } if !pattern.conjuncts_at(sort).is_empty() => sort.clone(),
            _ => return pattern,
        };
        externalize::conjunction(
            &sort,
            pattern.into_conjuncts_at(&sort),
            externalize::ConjunctionShape::LeftNested,
        )
        .expect("the conjuncts were checked to be non-empty")
    })
}

fn pattern_variables(pattern: &Pattern) -> BTreeSet<Variable> {
    pattern
        .term
        .attributes()
        .variables
        .iter()
        .cloned()
        .chain(
            pattern
                .constraints
                .iter()
                .flat_map(Predicate::free_variables),
        )
        .collect()
}

fn split_constraints(
    constraints: &[Predicate],
    configuration_variables: &BTreeSet<Variable>,
    sorts: &SortGraph,
) -> (Vec<Predicate>, Substitution) {
    let (extracted, mut predicates) = extract_substitution(constraints, sorts);
    let mut substitution = Substitution::new();
    for (variable, value) in extracted {
        if configuration_variables.contains(&variable) || is_rewrite_existential(&variable) {
            substitution.insert(variable, value);
        } else {
            predicates.push(Predicate::Equals(Term::variable(variable), value));
        }
    }
    (predicates, substitution)
}

fn is_rewrite_existential(variable: &Variable) -> bool {
    let (_, decoded) = k_rust::kast::identifier::decode_variable(&variable.name);
    decoded.is_ok_and(|name| name.starts_with('?'))
}

fn implication_result(
    antecedent: &KorePattern,
    consequent: &KorePattern,
    result_sort: &BackendSort,
    result: ImplicationResult,
) -> Result<Value, RpcFault> {
    let status = match result.status {
        ImplicationStatus::Valid => "valid",
        ImplicationStatus::Invalid => "invalid",
        ImplicationStatus::Indeterminate => "indeterminate",
    };
    let implication = KorePattern::Implies {
        sort: externalize::sort(result_sort),
        left: Box::new(antecedent.clone()),
        right: Box::new(consequent.clone()),
    };
    let mut output = json!({
        "implication": encode_kore(&implication)?,
        "status": status,
    });
    if let Some(condition) = result.condition {
        let antecedent_variable = match antecedent.strip_exists() {
            KorePattern::Variable(variable) => Some(variable.name.as_str()),
            _ => None,
        };
        let substitution = backend_implication::condition_substitution(
            &condition.substitution,
            result_sort,
            antecedent_variable,
        )
        .unwrap_or_else(|| KorePattern::Top {
            sort: externalize::sort(result_sort),
        });
        let predicate = externalize::predicates_pattern(
            &condition.predicates,
            result_sort,
            |predicate| externalize::predicate_pattern(predicate, result_sort),
            externalize::ConjunctionShape::LeftNested,
        )
        .unwrap_or_else(|| KorePattern::Top {
            sort: externalize::sort(result_sort),
        });
        output["condition"] = json!({
            "substitution": encode_kore(&substitution)?,
            "predicate": encode_kore(&predicate)?,
        });
    }
    Ok(output)
}

pub(super) fn serve(backend: Backend, address: impl ToSocketAddrs) -> Result<(), Box<dyn Error>> {
    let listener = TcpListener::bind(address)?;
    eprintln!("KORE JSON-RPC listening on {}", listener.local_addr()?);
    let service = Arc::new(Mutex::new(RpcService::with_backend(backend)));
    for connection in listener.incoming() {
        let stream = connection?;
        let service = Arc::clone(&service);
        thread::Builder::new()
            .name("krust-kore-rpc".into())
            .stack_size(CONNECTION_STACK_SIZE)
            .spawn(move || {
                if let Err(error) = serve_connection(stream, service) {
                    eprintln!("KORE JSON-RPC connection failed: {error}");
                }
            })?;
    }
    Ok(())
}

/// Serves one connection until its client stops sending. Closing either direction of the
/// connection ends the session: nothing more can be requested, so every active and queued
/// request of the connection is cancelled and none of them is answered.
fn serve_connection(
    stream: TcpStream,
    service: Arc<Mutex<RpcService>>,
) -> Result<(), Box<dyn Error>> {
    enable_keepalive(&stream)?;
    let mut reader = stream.try_clone()?;
    let writer = Arc::new(Mutex::new(BufWriter::new(stream)));
    let controls = Arc::new(Mutex::new(VecDeque::<Arc<RequestControl>>::new()));
    let (sender, receiver) = mpsc::channel::<(String, Arc<RequestControl>)>();
    let worker_writer = Arc::clone(&writer);
    let worker_controls = Arc::clone(&controls);
    let worker = thread::Builder::new()
        .name("krust-kore-rpc-worker".into())
        .stack_size(CONNECTION_STACK_SIZE)
        .spawn(move || -> io::Result<()> {
            for (line, control) in receiver {
                // A request cancelled before it runs (its session ended while it was queued, or
                // while this worker waited for another connection's request) is not run.
                let response = if control.is_cancelled() {
                    None
                } else {
                    control.token.scope(|| {
                        service
                            .lock()
                            .map_err(|_| {
                                io::Error::other("KORE JSON-RPC session lock was poisoned")
                            })
                            .map(|mut service| {
                                if control.is_cancelled() {
                                    None
                                } else {
                                    service.handle_line(&line)
                                }
                            })
                    })?
                };
                if control.complete()
                    && let Some(response) = response
                {
                    write_response(&worker_writer, &response)?;
                }
                let removed = worker_controls
                    .lock()
                    .map_err(|_| io::Error::other("KORE JSON-RPC request queue was poisoned"))?
                    .pop_front();
                debug_assert!(removed.is_some_and(|queued| Arc::ptr_eq(&queued, &control)));
            }
            Ok(())
        })?;

    let mut buffer = Vec::new();
    let mut connection_error = None;
    loop {
        let message = match read_json_message(&mut reader, &mut buffer) {
            Ok(Some(message)) => message,
            Ok(None) => break,
            Err(error) => {
                connection_error = Some(error);
                break;
            }
        };
        if is_standalone_cancel(&message) {
            let active = controls
                .lock()
                .map_err(|_| io::Error::other("KORE JSON-RPC request queue was poisoned"))?
                .front()
                .cloned();
            if let Some(active) = active
                && active.cancel()
                && let Some(response) = &active.cancellation_response
                && let Err(error) = write_response(&writer, response)
            {
                connection_error = Some(error);
                break;
            }
            continue;
        }
        let control = Arc::new(RequestControl::new(&message));
        controls
            .lock()
            .map_err(|_| io::Error::other("KORE JSON-RPC request queue was poisoned"))?
            .push_back(Arc::clone(&control));
        if sender.send((message, control)).is_err() {
            break;
        }
    }
    // The session is over: no request of this connection may outlive it, and the worker must
    // not hold the shared service for requests nobody can ask about any more.
    for control in controls
        .lock()
        .map_err(|_| io::Error::other("KORE JSON-RPC request queue was poisoned"))?
        .iter()
    {
        control.cancel();
    }
    drop(sender);
    worker
        .join()
        .map_err(|_| io::Error::other("KORE JSON-RPC worker panicked"))??;
    if let Some(error) = connection_error {
        return Err(error.into());
    }
    Ok(())
}

fn enable_keepalive(stream: &TcpStream) -> io::Result<()> {
    let keepalive = socket2::TcpKeepalive::new()
        .with_time(KEEPALIVE_IDLE)
        .with_interval(KEEPALIVE_INTERVAL)
        .with_retries(KEEPALIVE_RETRIES);
    let socket = socket2::SockRef::from(stream);
    socket.set_tcp_keepalive(&keepalive)?;
    #[cfg(any(target_os = "linux", target_os = "android"))]
    socket.set_tcp_user_timeout(Some(UNACKNOWLEDGED_DATA_TIMEOUT))?;
    Ok(())
}

fn read_json_message(reader: &mut impl Read, buffer: &mut Vec<u8>) -> io::Result<Option<String>> {
    loop {
        let mut deserializer = serde_json::Deserializer::from_slice(buffer);
        deserializer.disable_recursion_limit();
        let mut values = deserializer.into_iter::<Value>();
        match values.next() {
            Some(Ok(_)) => {
                let consumed = values.byte_offset();
                let message = buffer.drain(..consumed).collect::<Vec<_>>();
                return String::from_utf8(message).map(Some).map_err(|error| {
                    io::Error::new(io::ErrorKind::InvalidData, error.utf8_error())
                });
            }
            Some(Err(error)) if !error.is_eof() => {
                let consumed = buffer
                    .iter()
                    .position(|byte| *byte == b'\n')
                    .map_or(buffer.len(), |newline| newline + 1);
                let message = buffer.drain(..consumed).collect::<Vec<_>>();
                return String::from_utf8(message).map(Some).map_err(|error| {
                    io::Error::new(io::ErrorKind::InvalidData, error.utf8_error())
                });
            }
            Some(Err(_)) | None => {}
        }

        let mut chunk = [0; 4096];
        let read = reader.read(&mut chunk)?;
        if read == 0 {
            if buffer.iter().all(u8::is_ascii_whitespace) {
                buffer.clear();
                return Ok(None);
            }
            let message = std::mem::take(buffer);
            return String::from_utf8(message)
                .map(Some)
                .map_err(|error| io::Error::new(io::ErrorKind::InvalidData, error.utf8_error()));
        }
        buffer.extend_from_slice(&chunk[..read]);
    }
}

fn write_response(writer: &Mutex<BufWriter<TcpStream>>, response: &str) -> io::Result<()> {
    let mut writer = writer
        .lock()
        .map_err(|_| io::Error::other("KORE JSON-RPC response writer was poisoned"))?;
    writer.write_all(response.as_bytes())?;
    writer.write_all(b"\n")?;
    writer.flush()
}

fn is_standalone_cancel(message: &str) -> bool {
    let Ok(Value::Object(request)) = parse_json_value(message) else {
        return false;
    };
    request.get("jsonrpc").and_then(Value::as_str) == Some(JSON_RPC_VERSION)
        && request.get("method").and_then(Value::as_str) == Some("cancel")
        && request
            .get("id")
            .is_none_or(|id| id.is_null() || id.is_number() || id.is_string())
}

fn cancellation_response(message: &str) -> Option<String> {
    let message = parse_json_value(message).ok()?;
    let response = match message {
        Value::Object(request) => cancellation_error_for_request(&request),
        Value::Array(requests) => {
            let responses = requests
                .iter()
                .filter_map(Value::as_object)
                .filter_map(cancellation_error_for_request)
                .collect::<Vec<_>>();
            (!responses.is_empty()).then_some(Value::Array(responses))
        }
        _ => None,
    }?;
    serde_json::to_string(&response).ok()
}

fn cancellation_error_for_request(request: &Map<String, Value>) -> Option<Value> {
    let id = request.get("id")?.clone();
    Some(RpcFault::cancelled().into_value(id))
}

#[cfg(test)]
mod tests {
    use std::{
        io::{BufRead, BufReader, Read, Write},
        net::{Shutdown, TcpListener, TcpStream},
        sync::{Arc, Mutex},
    };

    use k_rust::kore::{
        ast::Symbol,
        parser::{parse_definition, parse_pattern},
    };
    use k_rust_backend::term::Term;

    use super::*;

    const DEFINITION: &str = r#"[]
        module TEST
          sort SortState{} [hasDomainValues{}()]
          symbol state{}() : SortState{}
            [function{}(), total{}(), injective{}(), no-evaluators{}()]
          symbol next{}() : SortState{}
            [function{}(), total{}(), injective{}(), no-evaluators{}()]
          axiom{} \rewrites{SortState{}}(
            \and{SortState{}}(state{}(), \top{SortState{}}()),
            \and{SortState{}}(next{}(), \top{SortState{}}())
          )
            [label{}("TEST.step"), UNIQUE'Unds'ID{}("rule-id")]
        endmodule []"#;

    fn service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(DEFINITION).unwrap(),
            "TEST",
        ))
    }

    fn implication_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  sort SortK{} []
                  symbol value{}() : SortK{} [constructor{}()]
                  symbol other{}() : SortK{} [constructor{}()]
                  symbol macroValue{}() : SortK{} [functional{}(), macro{}()]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn simplifying_implication_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  sort SortState{} []
                  symbol initial{}() : SortState{} [function{}(), total{}()]
                  symbol state{}() : SortState{} [constructor{}()]
                  axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortState{}, R}(
                      initial{}(),
                      \and{SortState{}}(state{}(), \top{SortState{}}())
                    )
                  ) [label{}("init"), simplification{}()]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn budget_policy_service() -> RpcService {
        let mut theory = String::new();
        for index in 0..=128 {
            theory.push_str(&format!(
                "symbol chain{index}{{}}() : SortState{{}} [function{{}}()]\n"
            ));
        }
        for index in 0..128 {
            let next = index + 1;
            theory.push_str(&format!(
                r#"
                axiom{{R}} \implies{{R}}(
                    \top{{R}}(),
                    \equals{{SortState{{}}, R}}(
                        chain{index}{{}}(),
                        \and{{SortState{{}}}}(chain{next}{{}}(), \top{{SortState{{}}}}())
                    )
                ) [label{{}}("chain-{index}"), simplification{{}}()]
                "#
            ));
        }
        theory.push_str(
            r#"
            axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortState{}, R}(
                    chain128{}(),
                    \and{SortState{}}(done{}(), \top{SortState{}}())
                )
            ) [label{}("chain-done"), simplification{}()]
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(
                    wrap{}(X:SortState{}),
                    \equals{SortState{}, SortState{}}(chain0{}(), done{}())
                ),
                done{}()
            ) [label{}("conditional")]
            "#,
        );
        let source = format!(
            r#"[]
            module TEST
                sort SortState{{}} [hasDomainValues{{}}()]
                symbol wrap{{}}(SortState{{}}) : SortState{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                symbol done{{}}() : SortState{{}}
                    [function{{}}(), total{{}}(), injective{{}}(), no-evaluators{{}}()]
                {theory}
            endmodule []"#
        );
        RpcService::new(BackendSession::new(
            parse_definition(&source).expect("budget definition should parse"),
            "TEST",
        ))
    }

    fn smt_implication_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                  symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn boolean_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn unsupported_hook_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  sort SortState{} [hasDomainValues{}()]
                  hooked-symbol missing{}(SortState{}) : SortState{}
                    [function{}(), hook{}("TEST.missing")]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn console_hook_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  hooked-sort SortString{} [hook{}("STRING.String"), hasDomainValues{}()]
                  sort SortK{} []
                  symbol dotk{}() : SortK{} [constructor{}(), total{}()]
                  hooked-symbol write{}(SortInt{}, SortString{}) : SortK{}
                    [function{}(), total{}(), hook{}("IO.write")]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn symbolic_branch_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                  symbol wrap{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                  symbol lt{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), smt-hook{}("<")]
                  axiom{} \rewrites{SortInt{}}(
                    \and{SortInt{}}(
                      wrap{}(X:SortInt{}),
                      \equals{SortBool{}, SortInt{}}(
                        lt{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                      )
                    ),
                    \dv{SortInt{}}("-1")
                  ) [label{}("TEST.negative"), UNIQUE'Unds'ID{}("negative-rule")]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn invalid_injection_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  sort SortKItem{} []
                  sort SortK{} []
                  symbol inj{From, To}(From) : To [sortInjection{}()]
                  symbol wrap{}(SortK{}) : SortK{} [constructor{}()]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn simplify_validation_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  sort SortKItem{} []
                  sort SortInt{} [hasDomainValues{}()]
                  sort SortBool{} [hasDomainValues{}()]
                  symbol inj{From, To}(From) : To [sortInjection{}()]
                  symbol Lblite{Sort}(SortBool{}, Sort, Sort) : Sort [function{}(), total{}()]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    fn implication_error(antecedent: &str, consequent: &str) -> Value {
        implication_response(antecedent, consequent)["error"].clone()
    }

    fn implication_response(antecedent: &str, consequent: &str) -> Value {
        let mut service = implication_service();
        let antecedent = encode_kore(&parse_pattern(antecedent).unwrap()).unwrap();
        let consequent = encode_kore(&parse_pattern(consequent).unwrap()).unwrap();
        request(
            &mut service,
            1,
            "implies",
            json!({ "antecedent": antecedent, "consequent": consequent }),
        )
    }

    #[test]
    fn reports_protocol_errors_and_preserves_string_ids() {
        let mut service = service();
        let parse: Value = serde_json::from_str(&service.handle_line("{").unwrap()).unwrap();
        assert_eq!(parse["error"]["code"], -32700);
        assert_eq!(parse["id"], Value::Null);

        let missing: Value = serde_json::from_str(
            &service
                .handle_line(r#"{"jsonrpc":"2.0","id":"request-7","method":"missing"}"#)
                .unwrap(),
        )
        .unwrap();
        assert_eq!(missing["id"], "request-7");
        assert_eq!(missing["error"]["code"], -32601);
        assert_eq!(missing["error"]["data"], "missing");
    }

    /// The fixture is the verbatim line returned by the pinned reference servers
    /// (`kore-rpc` and `kore-rpc-booster` v0.1.155, K v7.1.337's haskell-backend pin) for
    /// the `error-unknown` request of the RPC differential matrix, recorded from the
    /// bounded-search definition. Every field is compared, not only the code.
    #[test]
    fn unknown_method_fault_matches_the_recorded_reference_response() {
        let recorded: Value = serde_json::from_str(include_str!(
            "../tests/fixtures/reference/rpc/error-unknown.json"
        ))
        .unwrap();
        let mut service = service();
        let actual: Value = serde_json::from_str(
            &service
                .handle_line(r#"{"jsonrpc":"2.0","id":"unknown-1","method":"unknown"}"#)
                .unwrap(),
        )
        .unwrap();

        assert_eq!(actual, recorded);
    }

    #[test]
    fn invalid_requests_report_the_reference_error_shape() {
        let cases = vec![
            ("empty batch", json!([]), Some(json!([]))),
            ("non-object", json!(42), Some(json!(42))),
            (
                "missing version",
                json!({ "id": 1, "method": "execute" }),
                Some(json!({ "id": 1, "method": "execute" })),
            ),
            (
                "wrong version",
                json!({ "jsonrpc": "1.0", "id": 1, "method": "execute" }),
                Some(json!({ "jsonrpc": "1.0", "id": 1, "method": "execute" })),
            ),
            (
                "missing method",
                json!({ "jsonrpc": "2.0", "id": 1 }),
                Some(json!({ "jsonrpc": "2.0", "id": 1 })),
            ),
            (
                "object id",
                json!({ "jsonrpc": "2.0", "id": {}, "method": "execute" }),
                Some(json!({ "jsonrpc": "2.0", "id": {}, "method": "execute" })),
            ),
            (
                "array id",
                json!({ "jsonrpc": "2.0", "id": [], "method": "execute" }),
                Some(json!({ "jsonrpc": "2.0", "id": [], "method": "execute" })),
            ),
        ];

        for (name, message, expected_data) in cases {
            let mut service = service();
            let response: Value = serde_json::from_str(
                &service
                    .handle_line(&message.to_string())
                    .unwrap_or_else(|| panic!("{name} must receive an error response")),
            )
            .unwrap();
            assert_eq!(response["jsonrpc"], "2.0", "{name}");
            assert_eq!(response["id"], Value::Null, "{name}");
            assert_eq!(response["error"]["code"], -32600, "{name}");
            assert_eq!(response["error"]["message"], "Invalid request", "{name}");
            assert_eq!(
                response["error"].get("data"),
                expected_data.as_ref(),
                "{name}"
            );
        }
    }

    #[test]
    fn invalid_params_report_code_32602_for_every_method() {
        let state = trivial_model_state();
        let cases = vec![
            ("simplify missing state", "simplify", json!({})),
            ("simplify wrong state", "simplify", json!({ "state": 7 })),
            (
                "implies missing consequent",
                "implies",
                json!({ "antecedent": state.clone() }),
            ),
            (
                "implies wrong consequent",
                "implies",
                json!({ "antecedent": state.clone(), "consequent": 7 }),
            ),
            ("add-module missing module", "add-module", json!({})),
            (
                "add-module wrong module",
                "add-module",
                json!({ "module": 7 }),
            ),
            ("get-model missing state", "get-model", json!({})),
            ("get-model wrong state", "get-model", json!({ "state": 7 })),
        ];

        for (name, method, params) in cases {
            let mut service = service();
            let response = request(&mut service, 17, method, params.clone());
            assert_eq!(response["id"], 17, "{name}");
            assert_eq!(response["error"]["code"], -32602, "{name}");
            assert_eq!(response["error"]["message"], "Invalid params", "{name}");
            assert_eq!(response["error"]["data"], params, "{name}");
        }
    }

    #[test]
    fn absent_and_null_params_omit_invalid_params_data() {
        for request in [
            json!({ "jsonrpc": "2.0", "id": 17, "method": "execute" }),
            json!({ "jsonrpc": "2.0", "id": 17, "method": "execute", "params": null }),
        ] {
            let mut service = service();
            let response: Value = serde_json::from_str(
                &service
                    .handle_line(&request.to_string())
                    .expect("requests with ids receive responses"),
            )
            .unwrap();

            assert_eq!(response["error"]["code"], -32602, "{response:#}");
            assert_eq!(
                response["error"]["message"], "Invalid params",
                "{response:#}"
            );
            assert!(response["error"].get("data").is_none(), "{response:#}");
        }
    }

    #[test]
    fn unknown_param_keys_are_invalid_params() {
        let state = encode_kore(&parse_pattern("state{}()").unwrap()).unwrap();
        let model_state = trivial_model_state();
        let with_key = |params: &Value, key: &str| {
            let mut params = params.clone();
            params.as_object_mut().unwrap().insert(key.into(), json!(0));
            params
        };
        // `max-depth: 0` halts this state on the depth bound; the misspelt `max-dept` would
        // otherwise run it unbounded and report a different result.
        let cases = vec![
            (
                "execute",
                json!({ "state": state.clone(), "max-depth": 0 }),
                "max-dept",
            ),
            (
                "simplify",
                json!({ "state": state.clone() }),
                "future-option",
            ),
            (
                "implies",
                json!({ "antecedent": state.clone(), "consequent": state.clone() }),
                "assume-defind",
            ),
            (
                "add-module",
                json!({ "module": "module EXTRA import TEST [] endmodule []" }),
                "name-as-ids",
            ),
            (
                "get-model",
                json!({ "state": model_state }),
                "future-option",
            ),
        ];

        for (method, declared, unknown) in cases {
            let accepted = request(&mut service(), 1, method, declared.clone());
            assert!(accepted.get("error").is_none(), "{method}: {accepted:#}");
            if method == "execute" {
                assert_eq!(accepted["result"]["reason"], "depth-bound");
            }

            let params = with_key(&declared, unknown);
            let rejected = request(&mut service(), 1, method, params.clone());
            assert!(rejected.get("result").is_none(), "{method}: {rejected:#}");
            assert_eq!(rejected["error"]["code"], -32602, "{method}");
            assert_eq!(rejected["error"]["message"], "Invalid params", "{method}");
            assert_eq!(rejected["error"]["data"], params, "{method}");
        }

        // Every declared key, including the k-rust extension and the routing and logging keys,
        // is still accepted.
        let response = request(
            &mut service(),
            1,
            "execute",
            json!({
                "state": state,
                "max-depth": 0,
                "max-simplification-iterations": 4,
                "booster-only": true,
                "haskell-logging": ["Rewrite"],
            }),
        );
        assert!(response.get("error").is_none(), "{response:#}");
        assert_eq!(response["result"]["reason"], "depth-bound");
    }

    #[test]
    fn malformed_kore_envelopes_are_invalid_params() {
        let mut service = service();
        let params = json!({ "state": "aaaa", "max-depth": 1 });
        let response = request(&mut service, 1, "execute", params.clone());

        assert_eq!(response["error"]["code"], -32602);
        assert_eq!(response["error"]["message"], "Invalid params");
        assert_eq!(response["error"]["data"], params);
    }

    #[test]
    fn pattern_verification_errors_identify_the_offending_kore_subterm() {
        let mut arity_service = service();
        let invalid_application = parse_pattern("state{}(next{}())").unwrap();
        let arity_error = request(
            &mut arity_service,
            1,
            "execute",
            json!({ "state": encode_kore(&invalid_application).unwrap() }),
        );
        assert_eq!(
            arity_error["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{
                    "term": encode_kore(&invalid_application).unwrap(),
                    "error": "Inconsistent pattern. Symbol 'state' expected 0 arguments but got 1",
                }],
            })
        );

        let mut sort_service = symbolic_branch_service();
        let invalid_argument = parse_pattern(r#"\dv{SortBool{}}("true")"#).unwrap();
        let invalid_application = parse_pattern(r#"wrap{}(\dv{SortBool{}}("true"))"#).unwrap();
        let sort_error = request(
            &mut sort_service,
            2,
            "execute",
            json!({ "state": encode_kore(&invalid_application).unwrap() }),
        );
        assert_eq!(
            sort_error["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{
                    "term": encode_kore(&invalid_argument).unwrap(),
                    "error": "Incorrect sort: expected SortInt{} but got SortBool{}",
                }],
            })
        );

        let mut injection_service = invalid_injection_service();
        let invalid_injection =
            parse_pattern(r#"inj{SortKItem{}, SortK{}}(VarX:SortKItem{})"#).unwrap();
        let invalid_pattern =
            parse_pattern(r#"wrap{}(inj{SortKItem{}, SortK{}}(VarX:SortKItem{}))"#).unwrap();
        let injection_error = request(
            &mut injection_service,
            3,
            "execute",
            json!({ "state": encode_kore(&invalid_pattern).unwrap() }),
        );
        assert_eq!(
            injection_error["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{
                    "term": encode_kore(&invalid_injection).unwrap(),
                    "error": "SortKItem{} is not a subsort of SortK{}",
                }],
            })
        );

        let mut unknown_symbol_service = service();
        let unknown_symbol = parse_pattern("missing{}()").unwrap();
        let unknown_symbol_error = request(
            &mut unknown_symbol_service,
            4,
            "execute",
            json!({ "state": encode_kore(&unknown_symbol).unwrap() }),
        );
        assert_eq!(
            unknown_symbol_error["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{
                    "term": encode_kore(&unknown_symbol).unwrap(),
                    "error": "Unknown symbol 'missing'",
                }],
            })
        );

        let mut unknown_sort_service = service();
        let unknown_sort = parse_pattern("VarX:SortMissing{}").unwrap();
        let unknown_sort_error = request(
            &mut unknown_sort_service,
            5,
            "execute",
            json!({ "state": encode_kore(&unknown_sort).unwrap() }),
        );
        assert_eq!(
            unknown_sort_error["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{ "error": "Unknown sort 'SortMissing'" }],
            })
        );
    }

    #[test]
    fn simplify_reports_the_validation_error_for_a_term_input() {
        let mut service = simplify_validation_service();
        let invalid_ite =
            parse_pattern(r#"Lblite{SortInt{}}(\dv{SortBool{}}("true"), \dv{SortInt{}}("0"))"#)
                .unwrap();
        let invalid_input = parse_pattern(
            r#"inj{SortInt{}, SortKItem{}}(Lblite{SortInt{}}(\dv{SortBool{}}("true"), \dv{SortInt{}}("0")))"#,
        )
        .unwrap();
        let arity_error = request(
            &mut service,
            1,
            "simplify",
            json!({ "state": encode_kore(&invalid_input).unwrap() }),
        );
        assert_eq!(
            arity_error["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{
                    "term": encode_kore(&invalid_ite).unwrap(),
                    "error": "Inconsistent pattern. Symbol 'Lblite' expected 3 arguments but got 2",
                }],
            })
        );

        let invalid_condition = parse_pattern(r#"\dv{SortInt{}}("42")"#).unwrap();
        let invalid_input = parse_pattern(
            r#"inj{SortInt{}, SortKItem{}}(Lblite{SortInt{}}(\dv{SortInt{}}("42"), \dv{SortInt{}}("1"), \dv{SortInt{}}("0")))"#,
        )
        .unwrap();
        let sort_error = request(
            &mut service,
            2,
            "simplify",
            json!({ "state": encode_kore(&invalid_input).unwrap() }),
        );
        assert_eq!(
            sort_error["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{
                    "term": encode_kore(&invalid_condition).unwrap(),
                    "error": "Incorrect sort: expected SortBool{} but got SortInt{}",
                }],
            })
        );
    }

    #[test]
    fn implication_rejects_a_non_function_like_antecedent_with_context() {
        let error = implication_error(
            r#"\or{SortK{}}(X:SortK{}, \not{SortK{}}(X:SortK{}))"#,
            "X:SortK{}",
        );
        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": [r#"\or{SortK{}}(X:SortK{}, \not{SortK{}}(X:SortK{}))"#],
                    "error": "The check implication step expects the antecedent term to be function-like.",
                },
            })
        );
    }

    #[test]
    fn implication_accepts_a_bottom_antecedent_as_vacuously_valid() {
        let response = implication_response(r#"\bottom{SortK{}}()"#, "X:SortK{}");

        assert_eq!(response["result"]["status"], "valid");
        assert_eq!(
            response["result"]["condition"]["predicate"]["term"]["tag"],
            "Bottom"
        );
        assert_eq!(
            response["result"]["condition"]["substitution"]["term"]["tag"],
            "Top"
        );
    }

    #[test]
    fn non_unifying_configurations_omit_condition() {
        let response = implication_response("value{}()", "other{}()");

        assert_eq!(response["result"]["status"], "invalid", "{response:#}");
        assert!(
            response["result"].get("condition").is_none(),
            "{response:#}"
        );
    }

    #[test]
    fn indeterminate_implication_uses_the_reference_wire_status() {
        let pattern = parse_pattern("value{}()").unwrap();
        let response = implication_result(
            &pattern,
            &pattern,
            &BackendSort::simple("SortK"),
            ImplicationResult {
                status: ImplicationStatus::Indeterminate,
                condition: None,
                failure: None,
                vacuous: false,
            },
        )
        .unwrap();

        assert_eq!(response["status"], "indeterminate", "{response:#}");
        assert!(response.get("condition").is_none(), "{response:#}");
    }

    #[test]
    fn bottom_antecedent_response_simplifies_the_consequent() {
        let mut service = simplifying_implication_service();
        let antecedent = encode_kore(&parse_pattern(r#"\bottom{SortState{}}()"#).unwrap()).unwrap();
        let consequent = encode_kore(&parse_pattern("initial{}()").unwrap()).unwrap();
        let response = request(
            &mut service,
            1,
            "implies",
            json!({ "antecedent": antecedent, "consequent": consequent }),
        );

        assert_eq!(response["result"]["status"], "valid", "{response:#}");
        assert_eq!(
            response["result"]["implication"]["term"]["second"]["name"], "state",
            "{response:#}"
        );
    }

    #[test]
    fn implication_accepts_a_top_consequent_as_valid() {
        let response = implication_response("X:SortK{}", r#"\top{SortK{}}()"#);

        assert_eq!(response["result"]["status"], "valid");
        assert_eq!(
            response["result"]["condition"]["predicate"]["term"]["tag"],
            "Top"
        );
        assert_eq!(
            response["result"]["condition"]["substitution"]["term"]["tag"],
            "Top"
        );
    }

    #[test]
    fn implication_retains_a_bottom_consequent_as_the_invalid_condition() {
        let response = implication_response("X:SortK{}", r#"\bottom{SortK{}}()"#);

        assert_eq!(response["result"]["status"], "invalid");
        assert_eq!(
            response["result"]["condition"]["predicate"]["term"]["tag"],
            "Bottom"
        );
        assert_eq!(
            response["result"]["condition"]["substitution"]["term"]["tag"],
            "Top"
        );
    }

    #[test]
    fn implication_special_cases_follow_the_reference_matrix() {
        let bottom = r#"\bottom{SortK{}}()"#;
        let top = r#"\top{SortK{}}()"#;
        let regular = "value{}()";
        let cases = [
            (bottom, bottom, "valid", "Bottom"),
            (bottom, top, "valid", "Bottom"),
            (bottom, regular, "valid", "Bottom"),
            (regular, bottom, "invalid", "Bottom"),
            (regular, top, "valid", "Top"),
            (regular, regular, "valid", "Top"),
        ];

        for (antecedent, consequent, status, predicate) in cases {
            let response = implication_response(antecedent, consequent);
            assert_eq!(response["result"]["status"], status, "{response:#}");
            assert_eq!(
                response["result"]["condition"]["predicate"]["term"]["tag"], predicate,
                "{response:#}"
            );
            assert_eq!(
                response["result"]["condition"]["substitution"]["term"]["tag"], "Top",
                "{response:#}"
            );
        }

        for consequent in [bottom, top, regular] {
            let response = implication_response(top, consequent);
            assert_eq!(response["error"]["code"], 4, "{response:#}");
            assert_eq!(
                response["error"]["data"]["error"],
                "The check implication step expects the antecedent term to be function-like.",
                "{response:#}"
            );
        }
    }

    #[test]
    fn implication_uses_an_smt_counterexample_as_a_public_refutation() {
        let mut service = smt_implication_service();
        let constrained = |bound| {
            encode_kore(
                &parse_pattern(&format!(
                    r#"\and{{SortInt{{}}}}(
                        X:SortInt{{}},
                        \equals{{SortBool{{}}, SortInt{{}}}}(
                            \dv{{SortBool{{}}}}("true"),
                            lt{{}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{bound}"))
                        )
                    )"#
                ))
                .expect("constrained integer pattern should parse"),
            )
            .expect("constrained integer pattern should encode")
        };

        let response = request(
            &mut service,
            1,
            "implies",
            json!({
                "antecedent": constrained(100),
                "consequent": constrained(10),
                "assume-defined": true,
            }),
        );

        assert_eq!(response["result"]["status"], "invalid");
        assert_eq!(
            response["result"]["condition"]["predicate"]["term"]["tag"],
            "Top"
        );
        assert_eq!(
            response["result"]["condition"]["substitution"]["term"]["tag"],
            "Top"
        );
    }

    fn boxed_integer_implication(antecedent: &str, consequent: &str) -> Value {
        let mut service = RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  sort SortK{} []
                  symbol box{}(SortInt{}) : SortK{} [constructor{}()]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ));
        let antecedent = encode_kore(&parse_pattern(antecedent).unwrap()).unwrap();
        let consequent = encode_kore(&parse_pattern(consequent).unwrap()).unwrap();
        request(
            &mut service,
            1,
            "implies",
            json!({ "antecedent": antecedent, "consequent": consequent }),
        )
    }

    /// A free variable of the consequent that the antecedent shares denotes the same value on both
    /// sides, so matching `box(X)` against `box(0)` yields the equation `X = 0`, which the
    /// antecedent must entail.
    #[test]
    fn implication_checks_the_binding_of_a_shared_universal_variable() {
        let antecedent = |value: &str| {
            format!(
                r#"\and{{SortK{{}}}}(
                    box{{}}(\dv{{SortInt{{}}}}("0")),
                    \equals{{SortInt{{}}, SortK{{}}}}(X:SortInt{{}}, \dv{{SortInt{{}}}}("{value}"))
                )"#
            )
        };
        let consequent = "box{}(X:SortInt{})";

        let refuted = boxed_integer_implication(&antecedent("1"), consequent);
        assert_eq!(refuted["result"]["status"], "invalid", "{refuted:#}");
        let substitution = &refuted["result"]["condition"]["substitution"]["term"];
        assert_eq!(substitution["tag"], "Equals", "{refuted:#}");
        assert_eq!(substitution["first"]["name"], "X", "{refuted:#}");
        assert_eq!(substitution["second"]["value"], "0", "{refuted:#}");

        let entailed = boxed_integer_implication(&antecedent("0"), consequent);
        assert_eq!(entailed["result"]["status"], "valid", "{entailed:#}");
    }

    #[test]
    fn implication_orients_configuration_substitutions_from_variable_to_value() {
        let response = implication_response("X:SortK{}", "value{}()");
        let substitution = &response["result"]["condition"]["substitution"]["term"];

        assert_eq!(response["result"]["status"], "invalid");
        assert_eq!(substitution["tag"], "Equals");
        assert_eq!(substitution["first"]["tag"], "EVar");
        assert_eq!(substitution["first"]["name"], "X");
        assert_eq!(substitution["second"]["tag"], "App");
        assert_eq!(substitution["second"]["name"], "value");
    }

    #[test]
    fn implication_orients_fresh_consequent_existentials_toward_the_antecedent() {
        let response =
            implication_response("X:SortK{}", r#"\exists{SortK{}}(Z:SortK{}, Z:SortK{})"#);
        let substitution = &response["result"]["condition"]["substitution"]["term"];

        assert_eq!(response["result"]["status"], "valid");
        assert_eq!(substitution["tag"], "Equals");
        assert_eq!(substitution["first"]["name"], "X");
        assert_eq!(substitution["second"]["name"], "Z");
    }

    #[test]
    fn implication_response_simplifies_both_function_terms() {
        let mut service = simplifying_implication_service();
        let initial = encode_kore(&parse_pattern("initial{}()").unwrap()).unwrap();
        let response = request(
            &mut service,
            1,
            "implies",
            json!({
                "antecedent": initial,
                "consequent": initial,
            }),
        );
        let implication = &response["result"]["implication"]["term"];

        assert_eq!(response["result"]["status"], "valid");
        assert_eq!(implication["first"]["name"], "state");
        assert_eq!(implication["second"]["name"], "state");
    }

    #[test]
    fn special_consequent_responses_still_simplify_non_vacuous_antecedents() {
        let mut service = simplifying_implication_service();
        for (consequent, status) in [
            (r#"\top{SortState{}}()"#, "valid"),
            (r#"\bottom{SortState{}}()"#, "invalid"),
        ] {
            let antecedent = encode_kore(&parse_pattern("initial{}()").unwrap()).unwrap();
            let consequent = encode_kore(&parse_pattern(consequent).unwrap()).unwrap();
            let response = request(
                &mut service,
                1,
                "implies",
                json!({
                    "antecedent": antecedent,
                    "consequent": consequent,
                }),
            );

            assert_eq!(response["result"]["status"], status, "{response:#}");
            assert_eq!(
                response["result"]["implication"]["term"]["first"]["name"],
                "state"
            );
        }
    }

    #[test]
    fn implication_simplification_preserves_leading_binder_order() {
        let mut service = simplifying_implication_service();
        let source = r#"\exists{SortState{}}(
            X:SortState{},
            \exists{SortState{}}(Y:SortState{}, initial{}())
        )"#;
        let pattern = encode_kore(&parse_pattern(source).unwrap()).unwrap();
        let response = request(
            &mut service,
            1,
            "implies",
            json!({
                "antecedent": pattern,
                "consequent": pattern,
            }),
        );
        let antecedent = &response["result"]["implication"]["term"]["first"];

        assert_eq!(response["result"]["status"], "valid", "{response:#}");
        assert_eq!(antecedent["tag"], "Exists");
        assert_eq!(antecedent["var"], "X");
        assert_eq!(antecedent["arg"]["tag"], "Exists");
        assert_eq!(antecedent["arg"]["var"], "Y");
        assert_eq!(antecedent["arg"]["arg"]["name"], "state");
    }

    #[test]
    fn not_consequent_early_response_still_simplifies_both_patterns() {
        let mut service = simplifying_implication_service();
        let antecedent = encode_kore(&parse_pattern("initial{}()").unwrap()).unwrap();
        let consequent =
            encode_kore(&parse_pattern(r#"\not{SortState{}}(initial{}())"#).unwrap()).unwrap();
        let response = request(
            &mut service,
            1,
            "implies",
            json!({
                "antecedent": antecedent,
                "consequent": consequent,
            }),
        );

        assert_eq!(response["result"]["status"], "invalid", "{response:#}");
        assert_eq!(
            response["result"]["implication"]["term"]["first"]["name"],
            "state"
        );
        assert_eq!(
            response["result"]["implication"]["term"]["second"]["arg"]["name"],
            "state"
        );
    }

    #[test]
    fn implication_response_rendering_surfaces_simplification_failure() {
        let syntax = parse_definition(
            r#"[]
            module TEST
              sort SortState{} []
              symbol state{}() : SortState{} [constructor{}()]
              symbol loop{}(SortState{}) : SortState{} [function{}(), total{}()]
              axiom{R} \implies{R}(
                \top{R}(),
                \equals{SortState{}, R}(
                  loop{}(X:SortState{}),
                  \and{SortState{}}(
                    loop{}(loop{}(X:SortState{})),
                    \top{SortState{}}()
                  )
                )
              ) [label{}("loop"), simplification{}()]
            endmodule []"#,
        )
        .unwrap();
        let definition = BackendDefinition::internalize(&syntax, "TEST").unwrap();
        let original = parse_pattern("loop{}(state{}())").unwrap();
        let (pattern, _) = definition
            .internalize_implication_pattern(&original, &[])
            .unwrap();

        let fault = simplified_implication_response_syntax(
            &definition,
            &original,
            &pattern,
            &k_rust_backend::smt::NoSolver,
        )
        .expect_err("a diverging simplification rule should fail the request");

        assert_eq!(fault.code, 6);
        assert_eq!(fault.message, "Aborted");
        assert!(
            fault
                .data
                .as_ref()
                .and_then(Value::as_str)
                .is_some_and(|error| error.contains("IterationLimit")),
            "{fault:#?}"
        );
    }

    #[test]
    fn implication_normalization_drops_constraints_that_simplified_away() {
        let sort = BackendSort::simple("SortK");
        let configuration = Term::variable(Variable::new("CONFIG", sort.clone()));
        let x = Term::variable(Variable::new("X", sort.clone()));
        let stale = Predicate::Equals(Term::domain_value(sort.clone(), "3"), x);
        let original = KorePattern::And {
            sort: externalize::sort(&sort),
            arguments: vec![
                externalize::term(&configuration),
                externalize::predicate_pattern(&stale, &sort),
            ],
        };

        let normalized = normalized_implication_syntax(
            &original,
            &Pattern {
                term: configuration.clone(),
                constraints: Vec::new(),
            },
        );

        assert_eq!(normalized, externalize::term(&configuration));
    }

    #[test]
    fn implication_keeps_nested_consequent_existentials_on_the_left() {
        let sort = BackendSort::simple("SortK");
        let variable = Variable::new("X!exists0", sort.clone());
        let value = Term::domain_value(sort.clone(), "value");
        let substitution = Substitution::from([(variable, value)]);

        let output = backend_implication::condition_substitution(&substitution, &sort, None)
            .expect("the binding should externalize");
        let output = encode_kore(&output).unwrap();

        assert_eq!(output["term"]["first"]["tag"], "EVar");
        assert_eq!(output["term"]["first"]["name"], "X");
        assert_eq!(output["term"]["second"]["tag"], "DV");
        assert_eq!(output["term"]["second"]["value"], "value");
    }

    #[test]
    fn implication_normalization_preserves_conjunction_shape() {
        let sort = BackendSort::simple("SortK");
        let configuration = Term::variable(Variable::new("CONFIG", sort.clone()));
        let x = Term::variable(Variable::new("X", sort.clone()));
        let constraints = vec![
            Predicate::Equals(Term::domain_value(sort.clone(), "3"), x.clone()),
            Predicate::Equals(Term::domain_value(sort.clone(), "0"), x),
        ];
        let mut canonical = constraints
            .iter()
            .map(|predicate| externalize::predicate_pattern(predicate, &sort))
            .collect::<Vec<_>>();
        canonical.sort();
        let original = KorePattern::And {
            sort: externalize::sort(&sort),
            arguments: vec![
                externalize::term(&configuration),
                KorePattern::And {
                    sort: externalize::sort(&sort),
                    arguments: canonical.iter().cloned().rev().collect(),
                },
            ],
        };

        let normalized = normalized_implication_syntax(
            &original,
            &Pattern {
                term: configuration.clone(),
                constraints,
            },
        );
        let KorePattern::And { arguments, .. } = &normalized else {
            panic!("the outer conjunction should be preserved");
        };
        assert_eq!(arguments.len(), 2);
        assert_eq!(arguments[0], externalize::term(&configuration));
        let KorePattern::And { arguments, .. } = &arguments[1] else {
            panic!("the nested conjunction should be preserved");
        };
        assert_eq!(arguments, &canonical);
    }

    #[test]
    fn implication_normalization_uses_backend_order_and_balanced_constraint_groups() {
        fn flatten_and<'a>(pattern: &'a KorePattern, leaves: &mut Vec<&'a KorePattern>) {
            if let KorePattern::And { arguments, .. } = pattern {
                for argument in arguments {
                    flatten_and(argument, leaves);
                }
            } else {
                leaves.push(pattern);
            }
        }

        let sort = BackendSort::simple("SortK");
        let configuration = Term::variable(Variable::new("CONFIG", sort.clone()));
        let x = Term::variable(Variable::new("X", sort.clone()));
        let value = |value| Term::domain_value(sort.clone(), value);
        let constraints = vec![
            Predicate::Equals(x.clone(), value("5")),
            Predicate::Equals(value("2"), x.clone()),
            Predicate::Equals(x.clone(), value("4")),
            Predicate::Equals(value("0"), x.clone()),
            Predicate::Equals(x.clone(), value("3")),
            Predicate::Equals(value("1"), x),
        ];
        let original_constraints = constraints
            .iter()
            .map(|predicate| externalize::predicate_pattern(predicate, &sort))
            .collect::<Vec<_>>();
        let original_condition =
            original_constraints
                .into_iter()
                .reduce(|left, right| KorePattern::And {
                    sort: externalize::sort(&sort),
                    arguments: vec![left, right],
                });
        let original = KorePattern::And {
            sort: externalize::sort(&sort),
            arguments: vec![
                externalize::term(&configuration),
                original_condition.expect("there are six constraints"),
            ],
        };

        let normalized = normalized_implication_syntax(
            &original,
            &Pattern {
                term: configuration.clone(),
                constraints: constraints.clone(),
            },
        );
        let KorePattern::And { arguments, .. } = &normalized else {
            panic!("the normalized pattern should retain its term conjunction");
        };
        assert_eq!(arguments[0], externalize::term(&configuration));
        let KorePattern::And {
            arguments: groups, ..
        } = &arguments[1]
        else {
            panic!("six constraints should be divided into two groups");
        };
        assert_eq!(groups.len(), 2);
        assert!(groups.iter().all(|group| matches!(
            group,
            KorePattern::And { arguments, .. } if arguments.len() == 2
        )));

        let mut expected = constraints.iter().collect::<Vec<_>>();
        expected.sort();
        let expected = expected
            .into_iter()
            .map(|predicate| externalize::predicate_pattern(predicate, &sort))
            .collect::<Vec<_>>();
        let mut actual = Vec::new();
        flatten_and(&arguments[1], &mut actual);
        assert_eq!(actual, expected.iter().collect::<Vec<_>>());
    }

    #[test]
    fn implication_rejects_a_top_antecedent_as_non_function_like() {
        let error = implication_error(r#"\top{SortK{}}()"#, "X:SortK{}");

        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": [r#"\top{SortK{}}()"#],
                    "error": "The check implication step expects the antecedent term to be function-like.",
                },
            })
        );
    }

    #[test]
    fn implication_rejects_a_non_singleton_consequent_with_context() {
        let error = implication_error(
            "X:SortK{}",
            r#"\or{SortK{}}(X:SortK{}, \not{SortK{}}(X:SortK{}))"#,
        );
        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": [r#"RHS: \or{SortK{}}(X:SortK{}, \not{SortK{}}(X:SortK{}))"#],
                    "error": "Term does not simplify to a singleton pattern",
                },
            })
        );
    }

    #[test]
    fn implication_rejects_existential_name_capture_with_context() {
        let error = implication_error("X:SortK{}", r#"\exists{SortK{}}(X:SortK{}, X:SortK{})"#);
        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": [
                        "LHS: X:SortK{}",
                        "RHS: X:SortK{}",
                        "existentials: [X]",
                    ],
                    "error": "Existentials capture free variables of the antecedent: X",
                },
            })
        );
    }

    /// A free variable that only the consequent mentions is universal over the implication, so it
    /// is decided like any other: valid under an unsatisfiable antecedent or when nothing
    /// constrains it, invalid when a satisfiable antecedent allows a value of its sort that
    /// violates the match's obligation. `SortInt` has such values; a sort whose no-junk axiom
    /// leaves the bound value as the only one does not
    /// (`implication_decides_a_free_consequent_variable_by_the_no_junk_axiom`).
    #[test]
    fn implication_decides_free_consequent_variables() {
        let refuted =
            boxed_integer_implication(r#"box{}(\dv{SortInt{}}("0"))"#, "box{}(Y:SortInt{})");
        assert_eq!(refuted["result"]["status"], "invalid", "{refuted:#}");

        let vacuous = boxed_integer_implication(
            r#"\and{SortK{}}(
                box{}(X:SortInt{}),
                \and{SortK{}}(
                    \equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("0")),
                    \equals{SortInt{}, SortK{}}(X:SortInt{}, \dv{SortInt{}}("1"))
                )
            )"#,
            "box{}(Y:SortInt{})",
        );
        assert_eq!(vacuous["result"]["status"], "valid", "{vacuous:#}");

        let unconstrained = boxed_integer_implication(
            r#"box{}(\dv{SortInt{}}("0"))"#,
            r#"\and{SortK{}}(
                box{}(\dv{SortInt{}}("0")),
                \or{SortK{}}(
                    \equals{SortInt{}, SortK{}}(Y:SortInt{}, \dv{SortInt{}}("0")),
                    \not{SortK{}}(
                        \equals{SortInt{}, SortK{}}(Y:SortInt{}, \dv{SortInt{}}("0"))
                    )
                )
            )"#,
        );
        assert_eq!(
            unconstrained["result"]["status"], "valid",
            "{unconstrained:#}"
        );

        // An antecedent existential is not the consequent's universal of the same name.
        let captured = boxed_integer_implication(
            r#"\exists{SortK{}}(Y:SortInt{}, box{}(Y:SortInt{}))"#,
            "box{}(Y:SortInt{})",
        );
        assert_eq!(captured["result"]["status"], "invalid", "{captured:#}");
    }

    fn wrapped_constructor_implication(constructors: &str, axiom: &str) -> Value {
        let mut service = RpcService::new(BackendSession::new(
            parse_definition(&format!(
                r#"[]
                module TEST
                  sort SortU{{}} []
                  sort SortK{{}} []
                  {constructors}
                  {axiom}
                  symbol wrap{{}}(SortU{{}}) : SortK{{}} [constructor{{}}()]
                endmodule []"#
            ))
            .unwrap(),
            "TEST",
        ));
        let antecedent = encode_kore(&parse_pattern("wrap{}(u{}())").unwrap()).unwrap();
        let consequent = encode_kore(&parse_pattern("wrap{}(Y:SortU{})").unwrap()).unwrap();
        request(
            &mut service,
            1,
            "implies",
            json!({ "antecedent": antecedent, "consequent": consequent }),
        )
    }

    /// The consequent-only universal `Y` ranges over the values of `SortU` in the models of the
    /// definition, and the match binds it to `u()`. With one nullary constructor and the no-junk
    /// axiom, `u()` is the only value, so the obligation `Y = u()` holds for every `Y` and the
    /// implication is valid even though the solver, which treats `SortU` as uninterpreted, has a
    /// counterexample. Without the axiom, or with a second constructor, a violating value exists.
    #[test]
    fn implication_decides_a_free_consequent_variable_by_the_no_junk_axiom() {
        let only_u = wrapped_constructor_implication(
            "symbol u{}() : SortU{} [constructor{}()]",
            r#"axiom{} \or{SortU{}}(u{}(), \bottom{SortU{}}()) [constructor{}()]"#,
        );
        assert_eq!(only_u["result"]["status"], "valid", "{only_u:#}");

        let junk = wrapped_constructor_implication("symbol u{}() : SortU{} [constructor{}()]", "");
        assert_eq!(junk["result"]["status"], "invalid", "{junk:#}");

        let two = wrapped_constructor_implication(
            "symbol u{}() : SortU{} [constructor{}()]
                  symbol v{}() : SortU{} [constructor{}()]",
            r#"axiom{} \or{SortU{}}(u{}(), v{}(), \bottom{SortU{}}()) [constructor{}()]"#,
        );
        assert_eq!(two["result"]["status"], "invalid", "{two:#}");
    }

    #[test]
    fn implication_rejects_fixpoint_antecedents_as_non_function_like() {
        let error = implication_error(
            r#"\mu{}(@A:SortK{}, @A:SortK{})"#,
            r#"\exists{SortK{}}(Z:SortK{}, Z:SortK{})"#,
        );
        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": [r#"\mu{}(@A:SortK{}, @A:SortK{})"#],
                    "error": "The check implication step expects the antecedent term to be function-like.",
                },
            })
        );
    }

    #[test]
    fn implication_macro_errors_name_the_symbol() {
        let error = implication_error(
            r#"\and{SortK{}}(X:SortK{}, \and{SortK{}}(X:SortK{}, \equals{SortK{}, SortK{}}(X:SortK{}, macroValue{}())))"#,
            "X:SortK{}",
        );
        assert_eq!(
            error,
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{
                    "context": ["symbol or alias 'macroValue'"],
                    "error": "A symbol cannot be an alias or a macro",
                }],
            })
        );
    }

    #[test]
    fn implication_rejects_syntactic_sort_mismatch_before_sort_lookup() {
        let error = implication_error("X:S1{}", r#"\exists{SortK{}}(Y:SortK{}, Y:SortK{})"#);
        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": ["LHS sort: S1{}", "RHS sort: SortK{}"],
                    "error": "Antecedent and consequent must have the same sort.",
                },
            })
        );
    }

    #[test]
    fn implication_internalized_sort_mismatch_is_a_pattern_fault() {
        let definition = parse_definition(
            r#"[]
            module TEST
              sort SortA{} []
              sort SortB{} []
              symbol a{}() : SortA{} [constructor{}()]
              symbol b{}() : SortB{} [constructor{}()]
            endmodule []"#,
        )
        .unwrap();
        let mut service = RpcService::new(BackendSession::new(definition, "TEST"));
        let antecedent = encode_kore(&parse_pattern("a{}()").unwrap()).unwrap();
        let consequent = encode_kore(&parse_pattern("b{}()").unwrap()).unwrap();
        let response = request(
            &mut service,
            1,
            "implies",
            json!({ "antecedent": antecedent, "consequent": consequent }),
        );

        assert_eq!(
            response["error"],
            json!({
                "code": 2,
                "message": "Could not verify pattern",
                "data": [{ "error": "antecedent and consequent sorts differ" }],
            })
        );
    }

    #[test]
    fn internal_solver_failures_use_runtime_error_taxonomy() {
        let syntax = parse_definition(
            r#"[]
            module MAIN
                hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                symbol f{}(SortInt{}) : SortInt{}
                    [function{}(), total{}(), smtlib{}("f")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(\dv{SortInt{}}("1"), \top{SortInt{}}())
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-one")]
                axiom{R} \implies{R}(
                    \top{R}(),
                    \equals{SortInt{}, R}(
                        f{}(X:SortInt{}),
                        \and{SortInt{}}(\dv{SortInt{}}("2"), \top{SortInt{}}())
                    )
                ) [simplification{}(), smt-lemma{}(), label{}("f-is-two")]
            endmodule []"#,
        )
        .unwrap();
        let mut service = RpcService {
            backend: Backend::from_definition(syntax, "MAIN", BackendOptions::default())
                .expect("an unused SMT prelude does not affect initialization"),
        };
        let zero_query = request(
            &mut service,
            0,
            "get-model",
            json!({ "state": encode_kore(&parse_pattern(r#"\dv{SortInt{}}("1")"#).unwrap()).unwrap() }),
        );
        assert_eq!(zero_query["result"]["satisfiable"], "Unknown");
        let state = encode_kore(
            &parse_pattern(r#"\equals{SortInt{}, SortInt{}}(X:SortInt{}, \dv{SortInt{}}("1"))"#)
                .unwrap(),
        )
        .unwrap();
        let fault = request(&mut service, 1, "get-model", json!({ "state": state }));

        assert_eq!(fault["error"]["code"], -32002, "{fault:#}");
        assert_eq!(fault["error"]["message"], "Runtime error", "{fault:#}");
        assert!(
            fault["error"]["data"]["error"]
                .as_str()
                .is_some_and(|error| error == "could not initialize Z3: InconsistentPrelude"),
            "{fault:#}"
        );
        assert!(fault["error"]["data"].get("term").is_none(), "{fault:#}");
    }

    #[test]
    fn execute_reports_a_prelude_failure_and_later_requests_keep_the_runtime_fault() {
        let definition = parse_definition(include_str!(
            "../tests/fixtures/inconsistent-smt-prelude-loop.kore"
        ))
        .unwrap();
        let mut service = RpcService::new(BackendSession::new(definition, "MAIN"));
        let state = |source: &str| encode_kore(&parse_pattern(source).unwrap()).unwrap();
        let (sender, receiver) = mpsc::channel();
        thread::spawn(move || {
            let first = request(
                &mut service,
                1,
                "execute",
                json!({ "state": state("probe{}(X:SortInt{})") }),
            );
            let later = request(
                &mut service,
                2,
                "execute",
                json!({
                    "state": state(r#"wrap{}(\dv{SortInt{}}("0"))"#),
                    "max-depth": 0,
                }),
            );
            sender.send((first, later)).unwrap();
        });
        let (first, later) = receiver
            .recv_timeout(Duration::from_secs(20))
            .expect("an SMT prelude failure must interrupt execution promptly");
        for response in [first, later] {
            assert_eq!(response["error"]["code"], -32002, "{response:#}");
            assert_eq!(
                response["error"]["message"], "Runtime error",
                "{response:#}"
            );
            assert_eq!(
                response["error"]["data"]["error"], "could not initialize Z3: InconsistentPrelude",
                "{response:#}"
            );
        }
    }

    #[test]
    fn rewrite_existential_names_use_the_shared_identifier_decoder() {
        let sort = BackendSort::simple("SortS");
        for name in ["?X", "Var?X", "Var'Ques'X"] {
            assert!(
                is_rewrite_existential(&Variable::new(name, sort.clone())),
                "{name}"
            );
        }
        assert!(!is_rewrite_existential(&Variable::new("VarX", sort)));
    }

    #[test]
    fn protocol_parser_accepts_deep_json_without_serde_recursion_limits() {
        let depth = 300;
        let source = format!("{}null{}", "[".repeat(depth), "]".repeat(depth));
        assert!(parse_json_value(&source).is_ok());
    }

    #[test]
    fn kore_encoder_accepts_deep_patterns_without_serde_recursion_limits() {
        let mut pattern = KorePattern::Application {
            symbol: Symbol {
                name: "value".into(),
                sort_parameters: vec![],
            },
            arguments: vec![],
        };
        for _ in 0..160 {
            pattern = KorePattern::Application {
                symbol: Symbol {
                    name: "wrap".into(),
                    sort_parameters: vec![],
                },
                arguments: vec![pattern],
            };
        }

        assert!(encode_kore(&pattern).is_ok());
    }

    #[test]
    fn execute_accepts_a_deep_state_payload() {
        std::thread::Builder::new()
            .stack_size(CONNECTION_STACK_SIZE)
            .spawn(|| {
                let definition = parse_definition(
                    r#"[]
                    module TEST
                      sort SortK{} []
                      symbol value{}() : SortK{} [constructor{}()]
                      symbol wrap{}(SortK{}) : SortK{} [constructor{}()]
                    endmodule []"#,
                )
                .unwrap();
                let mut service = RpcService::new(BackendSession::new(definition, "TEST"));
                let depth = 2_000;
                let prefix = r#"{"tag":"App","name":"wrap","sorts":[],"args":["#;
                let suffix = "]}";
                let term = format!(
                    "{}{}{}",
                    prefix.repeat(depth),
                    r#"{"tag":"App","name":"value","sorts":[],"args":[]}"#,
                    suffix.repeat(depth)
                );
                let request = format!(
                    r#"{{"jsonrpc":"2.0","id":1,"method":"execute","params":{{"state":{{"format":"KORE","version":1,"term":{term}}},"max-depth":0}}}}"#
                );

                let response = service
                    .handle_line(&request)
                    .expect("execute requests receive a response");
                let response = parse_json_value(&response).unwrap();
                assert!(response.get("error").is_none(), "{response}");
                assert_eq!(response["result"]["depth"], 0);
            })
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn notifications_and_notification_only_batches_have_no_response() {
        let mut service = service();
        assert_eq!(
            service.handle_line(r#"{"jsonrpc":"2.0","method":"cancel"}"#),
            None
        );
        assert_eq!(
            service.handle_line(r#"[{"jsonrpc":"2.0","method":"cancel"}]"#),
            None
        );
    }

    #[test]
    fn mixed_batches_answer_requests_in_order_and_skip_notifications() {
        let mut service = service();
        let batch = json!([
            { "jsonrpc": "2.0", "id": "first", "method": "missing" },
            { "jsonrpc": "2.0", "method": "missing-notification" },
            {
                "jsonrpc": "2.0",
                "id": 2,
                "method": "get-model",
                "params": { "state": trivial_model_state() },
            },
        ]);
        let response: Value = serde_json::from_str(
            &service
                .handle_line(&batch.to_string())
                .expect("the requests in a mixed batch need responses"),
        )
        .unwrap();
        let responses = response
            .as_array()
            .expect("batch response must be an array");

        assert_eq!(responses.len(), 2);
        assert_eq!(responses[0]["id"], "first");
        assert_eq!(responses[0]["error"]["code"], -32601);
        assert_eq!(responses[1]["id"], 2);
        assert_eq!(responses[1]["result"]["satisfiable"], "Sat");
    }

    #[test]
    fn cancel_in_batch_fixture_answers_32601() {
        let mut service = service();
        let request =
            include_str!("../tests/fixtures/reference/rpc/cancel-in-batch/cancel-request.json");
        let response: Value = serde_json::from_str(&service.handle_line(request).unwrap()).unwrap();
        let expected: Value = serde_json::from_str(include_str!(
            "../tests/fixtures/reference/rpc/cancel-in-batch/cancel-response.json"
        ))
        .unwrap();

        assert_eq!(response, expected);
    }

    #[test]
    fn adds_modules_statefully_and_returns_the_canonical_id() {
        let mut service = service();
        let module = "module EXTRA import TEST [] endmodule []";
        let request = json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "add-module",
            "params": { "module": module, "name-as-id": true }
        });
        let response: Value =
            serde_json::from_str(&service.handle_line(&request.to_string()).unwrap()).unwrap();
        let id = response["result"]["module"].as_str().unwrap();
        assert!(id.starts_with('m'));
        assert_eq!(id.len(), 65);

        let definition = service.backend.select_definition(Some("EXTRA")).unwrap();
        assert_eq!(definition.main_module.as_ref(), id);
    }

    #[test]
    fn add_module_reports_reference_validation_errors() {
        let mut service = service();

        let malformed = request(
            &mut service,
            0,
            "add-module",
            json!({ "module": "module EXTRA" }),
        );
        assert_eq!(malformed["error"]["code"], 8, "{malformed:#}");
        assert_eq!(malformed["error"]["message"], "Invalid module");
        assert!(
            malformed["error"]["data"]["error"]
                .as_str()
                .is_some_and(|error| !error.is_empty()),
            "{malformed:#}"
        );

        let unknown_import = request(
            &mut service,
            1,
            "add-module",
            json!({ "module": "module EXTRA import MISSING [] endmodule []" }),
        );
        assert_eq!(
            unknown_import["error"],
            json!({
                "code": 8,
                "message": "Invalid module",
                "data": { "error": "Module MISSING not found." },
            })
        );

        let first = "module EXTRA import TEST [] endmodule []";
        assert!(
            request(
                &mut service,
                2,
                "add-module",
                json!({ "module": first, "name-as-id": true }),
            )["result"]["module"]
                .is_string()
        );
        let replacement = r#"module EXTRA
            import TEST []
            axiom{} \rewrites{SortState{}}(
                \and{SortState{}}(state{}(), \top{SortState{}}()),
                \and{SortState{}}(next{}(), \top{SortState{}}())
            ) []
        endmodule []"#;
        let duplicate = request(
            &mut service,
            3,
            "add-module",
            json!({ "module": replacement, "name-as-id": true }),
        );
        assert_eq!(
            duplicate["error"],
            json!({
                "code": 9,
                "message": "Duplicate module name",
                "data": "EXTRA",
            })
        );

        let new_sort = request(
            &mut service,
            4,
            "add-module",
            json!({
                "module": "module NEW-SORT sort SortNew{} [] endmodule []",
            }),
        );
        assert_eq!(
            new_sort["error"],
            json!({
                "code": 8,
                "message": "Invalid module",
                "data": { "error": "Module introduces new sorts: SortNew" },
            })
        );

        let new_symbol = request(
            &mut service,
            5,
            "add-module",
            json!({
                "module": "module NEW-SYMBOL symbol fresh{}() : SortState{} [] endmodule []",
            }),
        );
        assert_eq!(
            new_symbol["error"],
            json!({
                "code": 8,
                "message": "Invalid module",
                "data": { "error": "Module introduces new symbols: fresh" },
            })
        );

        let unknown_symbol = request(
            &mut service,
            6,
            "add-module",
            json!({
                "module": r#"module BAD-AXIOM
                    axiom{} missing{}() []
                endmodule []"#,
            }),
        );
        assert_eq!(unknown_symbol["error"]["code"], 8, "{unknown_symbol:#}");
        assert_eq!(unknown_symbol["error"]["message"], "Invalid module");
        assert!(
            unknown_symbol["error"]["data"].get("context").is_none(),
            "{unknown_symbol:#}"
        );
        assert_eq!(
            unknown_symbol["error"]["data"]["error"], "Unknown symbol 'missing'",
            "{unknown_symbol:#}"
        );
        assert!(
            unknown_symbol["error"]["data"]["term"].is_object(),
            "{unknown_symbol:#}"
        );
    }

    #[test]
    fn non_smt_simplification_failures_use_the_aborted_taxonomy() {
        let sort = BackendSort::simple("SortState");
        let fault = simplify_fault(
            SimplificationError::IterationLimit {
                limit: 0,
                term: Term::domain_value(sort.clone(), "value"),
            },
            &sort,
        )
        .into_value(json!(1));

        assert_eq!(fault["error"]["code"], 6, "{fault:#}");
        assert_eq!(fault["error"]["message"], "Aborted", "{fault:#}");
        assert!(
            fault["error"]["data"]
                .as_str()
                .is_some_and(|error| error.contains("IterationLimit")),
            "{fault:#}"
        );
    }

    #[test]
    fn fault_responses_preserve_ids_of_every_scalar_type() {
        for id in [json!("request-id"), json!(0), Value::Null] {
            let mut invalid_params_service = service();
            let invalid_params = request_with_id(
                &mut invalid_params_service,
                id.clone(),
                "simplify",
                json!({}),
            );

            let mut pattern_service = service();
            let invalid_application = encode_kore(
                &parse_pattern("state{}(next{}())").expect("invalid arity remains valid syntax"),
            )
            .unwrap();
            let pattern = request_with_id(
                &mut pattern_service,
                id.clone(),
                "execute",
                json!({ "state": invalid_application }),
            );

            let mut missing_module_service = service();
            let state = encode_kore(&parse_pattern("state{}()").unwrap()).unwrap();
            let module = request_with_id(
                &mut missing_module_service,
                id.clone(),
                "execute",
                json!({ "state": state, "module": "MISSING" }),
            );

            let mut implication_service = implication_service();
            let antecedent = encode_kore(&parse_pattern("X:S1{}").unwrap()).unwrap();
            let consequent =
                encode_kore(&parse_pattern(r#"\exists{SortK{}}(Y:SortK{}, Y:SortK{})"#).unwrap())
                    .unwrap();
            let implication = request_with_id(
                &mut implication_service,
                id.clone(),
                "implies",
                json!({ "antecedent": antecedent, "consequent": consequent }),
            );

            let mut invalid_module_service = service();
            let invalid_module = request_with_id(
                &mut invalid_module_service,
                id.clone(),
                "add-module",
                json!({ "module": "module EXTRA import MISSING [] endmodule []" }),
            );

            for (name, response, code) in [
                ("invalid params", invalid_params, -32602),
                ("pattern", pattern, 2),
                ("missing module", module, 3),
                ("implication", implication, 4),
                ("invalid module", invalid_module, 8),
            ] {
                assert_eq!(response["id"], id, "{name}");
                assert_eq!(response["error"]["code"], code, "{name}, id {id}");
            }
        }
    }

    #[test]
    fn missing_module_faults_cover_every_definition_consumer() {
        let state = encode_kore(&parse_pattern("state{}()").unwrap()).unwrap();
        let cases = [
            (
                "execute",
                json!({ "state": state.clone(), "module": "MISSING" }),
            ),
            (
                "simplify",
                json!({ "state": state.clone(), "module": "MISSING" }),
            ),
            (
                "implies",
                json!({
                    "antecedent": state.clone(),
                    "consequent": state.clone(),
                    "module": "MISSING",
                }),
            ),
            ("get-model", json!({ "state": state, "module": "MISSING" })),
        ];

        for (method, params) in cases {
            let mut service = service();
            let response = request(&mut service, 1, method, params);
            assert_eq!(
                response["error"],
                json!({
                    "code": 3,
                    "message": "Could not find module",
                    "data": "MISSING",
                }),
                "{method}"
            );
        }
    }

    #[test]
    fn executes_zero_steps_using_the_kore_json_envelope() {
        let mut service = service();
        let state = encode_kore(&KorePattern::Application {
            symbol: Symbol {
                name: "state".into(),
                sort_parameters: vec![],
            },
            arguments: vec![],
        })
        .unwrap();
        let request = json!({
            "jsonrpc": "2.0",
            "id": 1,
            "method": "execute",
            "params": { "state": state, "max-depth": 0 }
        });
        let response: Value =
            serde_json::from_str(&service.handle_line(&request.to_string()).unwrap()).unwrap();
        assert_eq!(response["result"]["reason"], "depth-bound");
        assert_eq!(response["result"]["depth"], 0);
        assert_eq!(response["result"]["state"]["term"]["format"], "KORE");
    }

    #[test]
    fn execute_returns_the_satisfiable_remainder_at_a_symbolic_branch() {
        let mut service = symbolic_branch_service();
        let state = encode_kore(&parse_pattern("wrap{}(X:SortInt{})").unwrap()).unwrap();

        let response = request(
            &mut service,
            1,
            "execute",
            json!({
                "state": state,
                "max-depth": 1,
            }),
        );

        assert_eq!(response["result"]["reason"], "branching");
        assert_eq!(response["result"]["depth"], 0);
        let next_states = response["result"]["next-states"].as_array().unwrap();
        assert_eq!(next_states.len(), 2);
        assert_eq!(next_states[0]["rule-id"], "negative-rule");
        assert!(next_states[1].get("rule-id").is_none());
        assert!(next_states[1].get("predicate").is_some());
    }

    #[test]
    fn execute_rule_provenance_preserves_symbolic_float_equality() {
        let syntax = parse_definition(
            r#"[]
                module TEST
                  hooked-sort SortFloat{} [hook{}("FLOAT.Float"), hasDomainValues{}()]
                  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                  sort SortState{} []
                  symbol wrap{}(SortFloat{}) : SortState{}
                    [constructor{}(), functional{}(), injective{}()]
                  symbol done{}() : SortState{} [constructor{}(), functional{}()]
                  hooked-symbol floatEq{}(SortFloat{}, SortFloat{}) : SortBool{}
                    [function{}(), total{}(), hook{}("FLOAT.eq")]
                  axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                      wrap{}(X:SortFloat{}),
                      \equals{SortBool{}, SortState{}}(
                        floatEq{}(X:SortFloat{}, X:SortFloat{}),
                        \dv{SortBool{}}("true")
                      )
                    ),
                    done{}()
                  ) [label{}("TEST.float-reflexive"), UNIQUE'Unds'ID{}("float-reflexive")]
                endmodule []"#,
        )
        .expect("Float provenance definition should parse");
        let mut service = RpcService::new(BackendSession::new(syntax, "TEST"));
        let state = encode_kore(&parse_pattern("wrap{}(X:SortFloat{})").unwrap()).unwrap();

        let response = request(
            &mut service,
            1,
            "execute",
            json!({ "state": state, "max-depth": 1 }),
        );

        assert_eq!(response["result"]["reason"], "branching", "{response:#}");
        let rule_predicate = &response["result"]["next-states"][0]["rule-predicate"]["term"];
        assert_eq!(rule_predicate["tag"], "Equals", "{response:#}");
        assert_eq!(
            rule_predicate["argSort"]["name"], "SortBool",
            "{response:#}"
        );
        assert_eq!(rule_predicate["first"]["tag"], "DV", "{response:#}");
        assert_eq!(rule_predicate["first"]["value"], "true", "{response:#}");
        assert_eq!(rule_predicate["second"]["tag"], "App", "{response:#}");
        assert_eq!(rule_predicate["second"]["name"], "floatEq", "{response:#}");
    }

    #[test]
    fn execute_rule_provenance_uses_the_declared_boolean_sort() {
        let syntax = parse_definition(
            r#"[]
                module TEST
                  hooked-sort SortTruth{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                  sort SortBool{} [hasDomainValues{}()]
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  sort SortState{} []
                  symbol wrapTruth{}(SortInt{}) : SortState{}
                    [constructor{}(), functional{}(), injective{}()]
                  symbol wrapLookalike{}(SortInt{}) : SortState{}
                    [constructor{}(), functional{}(), injective{}()]
                  symbol doneTruth{}() : SortState{} [constructor{}(), functional{}()]
                  symbol doneLookalike{}() : SortState{} [constructor{}(), functional{}()]
                  hooked-symbol intEqTruth{}(SortInt{}, SortInt{}) : SortTruth{}
                    [function{}(), total{}(), hook{}("INT.eq")]
                  hooked-symbol opaqueEqLookalike{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("TEST.eq")]
                  axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                      wrapTruth{}(X:SortInt{}),
                      \equals{SortTruth{}, SortState{}}(
                        intEqTruth{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortTruth{}}("true")
                      )
                    ),
                    doneTruth{}()
                  ) [UNIQUE'Unds'ID{}("truth-rule")]
                  axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(
                      wrapLookalike{}(X:SortInt{}),
                      \equals{SortBool{}, SortState{}}(
                        opaqueEqLookalike{}(X:SortInt{}, \dv{SortInt{}}("0")),
                        \dv{SortBool{}}("true")
                      )
                    ),
                    doneLookalike{}()
                  ) [UNIQUE'Unds'ID{}("lookalike-rule")]
                endmodule []"#,
        )
        .expect("Boolean-sort provenance definition should parse");
        let mut service = RpcService::new(BackendSession::new(syntax, "TEST"));

        let state = encode_kore(&parse_pattern("wrapTruth{}(X:SortInt{})").unwrap()).unwrap();
        let renamed = request(
            &mut service,
            1,
            "execute",
            json!({ "state": state, "max-depth": 1 }),
        );
        assert_eq!(renamed["result"]["reason"], "branching", "{renamed:#}");
        let predicate = &renamed["result"]["next-states"][0]["rule-predicate"]["term"];
        assert_eq!(predicate["tag"], "Equals", "{renamed:#}");
        assert_eq!(predicate["argSort"]["name"], "SortInt", "{renamed:#}");
        assert_eq!(predicate["first"]["name"], "X", "{renamed:#}");
        assert_eq!(predicate["second"]["value"], "0", "{renamed:#}");

        let state = encode_kore(&parse_pattern("wrapLookalike{}(X:SortInt{})").unwrap()).unwrap();
        let lookalike = request(
            &mut service,
            2,
            "execute",
            json!({ "state": state, "max-depth": 1 }),
        );
        assert_eq!(lookalike["result"]["reason"], "branching", "{lookalike:#}");
        let predicate = &lookalike["result"]["next-states"][0]["rule-predicate"]["term"];
        assert_eq!(predicate["tag"], "Equals", "{lookalike:#}");
        assert_eq!(predicate["argSort"]["name"], "SortBool", "{lookalike:#}");
        assert_eq!(predicate["first"]["value"], "true", "{lookalike:#}");
        assert_eq!(
            predicate["second"]["name"], "opaqueEqLookalike",
            "{lookalike:#}"
        );
    }

    #[test]
    fn execute_can_assume_the_current_configuration_is_defined() {
        let definition = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                symbol partial{}(SortS{}) : SortS{} [function{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    \dv{SortS{}}("done")
                ) [label{}("variable-match"), UNIQUE'Unds'ID{}("variable-match")]
            endmodule []"#,
        )
        .unwrap();
        let mut service = RpcService::new(BackendSession::new(definition, "MAIN"));
        let state =
            encode_kore(&parse_pattern(r#"wrap{}(partial{}(\dv{SortS{}}("value")))"#).unwrap())
                .unwrap();

        let response = request(
            &mut service,
            1,
            "execute",
            json!({
                "state": state,
                "max-depth": 1,
                "assume-state-defined": true,
            }),
        );

        assert_eq!(response["result"]["reason"], "depth-bound");
        assert_eq!(response["result"]["depth"], 1);
        assert_eq!(response["result"]["state"]["term"]["term"]["tag"], "DV");
        assert_eq!(response["result"]["state"]["term"]["term"]["value"], "done");
        assert!(response["result"]["state"].get("predicate").is_none());
    }

    #[test]
    fn emits_requested_successful_rewrite_logs() {
        let mut service = service();
        let state = encode_kore(&KorePattern::Application {
            symbol: Symbol {
                name: "state".into(),
                sort_parameters: vec![],
            },
            arguments: vec![],
        })
        .unwrap();
        let response = request(
            &mut service,
            1,
            "execute",
            json!({
                "state": state,
                "max-depth": 1,
                "log-successful-rewrites": true,
            }),
        );

        assert_eq!(
            response["result"]["logs"],
            json!([{
                "tag": "rewrite",
                "origin": "booster",
                "result": { "tag": "success", "rule-id": "rule-id" },
            }])
        );
    }

    #[test]
    fn emits_failed_rewrite_logs_only_when_a_step_actually_fails() {
        let mut service = service();
        let state = encode_kore(&parse_pattern("state{}()").unwrap()).unwrap();
        let response = request(
            &mut service,
            1,
            "execute",
            json!({
                "state": state,
                "log-successful-rewrites": true,
                "log-failed-rewrites": true,
            }),
        );

        assert_eq!(
            response["result"]["logs"],
            json!([
                {
                    "tag": "rewrite",
                    "origin": "booster",
                    "result": {
                        "tag": "success",
                        "rule-id": "rule-id",
                    },
                },
                {
                    "tag": "rewrite",
                    "origin": "booster",
                    "result": {
                        "tag": "failure",
                        "reason": "No applicable rules found",
                    },
                },
                {
                    "tag": "rewrite",
                    "origin": "booster",
                    "result": {
                        "tag": "failure",
                        "reason": "No applicable rules found",
                    },
                },
            ])
        );

        let next = encode_kore(&parse_pattern("next{}()").unwrap()).unwrap();
        let without_failures = request(
            &mut service,
            2,
            "execute",
            json!({
                "state": next,
                "log-successful-rewrites": true,
            }),
        );
        assert!(without_failures["result"].get("logs").is_none());
    }

    #[test]
    fn failed_rewrite_logs_preserve_the_uncertain_rule_id() {
        let reason =
            HaltReason::Indeterminate(k_rust_backend::rewrite::IndeterminateReason::Match {
                rule_id: "uncertain-rule".into(),
                substitution: Substitution::new(),
                remainder: Vec::new(),
            });
        let logs = execute_failed_rewrite_logs(&reason);
        assert_eq!(logs.len(), 2, "Booster retries uncertain matches once");
        let log = &logs[0];

        assert_eq!(log["result"]["tag"], "failure");
        assert_eq!(
            log["result"]["reason"],
            "Uncertain about unification of rule"
        );
        assert_eq!(log["result"]["rule-id"], "uncertain-rule");
    }

    #[test]
    fn captures_selected_legacy_context_logs_in_band() {
        let mut service = service();
        let state = encode_kore(&parse_pattern("state{}()").unwrap()).unwrap();
        let proxy = request(
            &mut service,
            1,
            "execute",
            json!({
                "state": state,
                "max-depth": 1,
                "haskell-logging": ["Proxy"],
            }),
        );
        let proxy_entries = proxy["result"]["haskell-log-entries"].as_array().unwrap();
        assert!(!proxy_entries.is_empty());
        assert!(proxy_entries.iter().all(|entry| {
            entry["context"]
                .as_array()
                .is_some_and(|context| context.iter().any(|part| part == "proxy"))
        }));

        let rewrite = request(
            &mut service,
            2,
            "execute",
            json!({
                "state": state,
                "max-depth": 1,
                "haskell-logging": ["Rewrite"],
            }),
        );
        assert_eq!(
            rewrite["result"]["haskell-log-entries"][0]["context"][2]["rewrite"],
            "rule-id"
        );
        assert_eq!(
            rewrite["result"]["haskell-log-entries"][0]["message"]["tag"],
            "success"
        );

        let unknown = request(
            &mut service,
            3,
            "execute",
            json!({
                "state": state,
                "max-depth": 1,
                "haskell-logging": ["UnknownEntryType"],
            }),
        );
        assert_eq!(unknown["result"]["haskell-log-entries"], json!([]));

        let control = request(
            &mut service,
            4,
            "execute",
            json!({ "state": state, "max-depth": 1 }),
        );
        assert!(control["result"].get("haskell-log-entries").is_none());
    }

    #[test]
    fn projects_solved_configuration_equalities_as_substitutions() {
        let definition =
            BackendDefinition::internalize(&parse_definition(DEFINITION).unwrap(), "TEST").unwrap();
        let sort = BackendSort::simple("SortState");
        let variable = Variable::new("X", sort.clone());
        let value = Term::domain_value(sort.clone(), "resolved");
        let pattern = Pattern {
            term: Term::variable(variable.clone()),
            constraints: vec![Predicate::Equals(
                Term::variable(variable.clone()),
                value.clone(),
            )],
        };

        let state = execute_state(&definition, &pattern, &BTreeSet::from([variable])).unwrap();
        assert_eq!(state["term"]["term"]["tag"], "DV");
        assert_eq!(state["term"]["term"]["value"], "resolved");
        assert_eq!(state["substitution"]["term"]["tag"], "Equals");
        assert_eq!(state["substitution"]["term"]["first"]["name"], "X");
        assert_eq!(state["substitution"]["term"]["second"]["value"], "resolved");
        assert!(state.get("predicate").is_none());
    }

    #[test]
    fn projects_saturated_configuration_substitutions() {
        let definition =
            BackendDefinition::internalize(&parse_definition(DEFINITION).unwrap(), "TEST").unwrap();
        let sort = BackendSort::simple("SortState");
        let x = Variable::new("X", sort.clone());
        let y = Variable::new("Y", sort.clone());
        let value = Term::domain_value(sort.clone(), "resolved");
        let pattern = Pattern {
            term: Term::variable(y.clone()),
            constraints: vec![
                Predicate::Equals(Term::variable(y.clone()), Term::variable(x.clone())),
                Predicate::Equals(Term::variable(x.clone()), value),
            ],
        };

        let state = execute_state(&definition, &pattern, &BTreeSet::from([x, y])).unwrap();

        assert_eq!(state["term"]["term"]["value"], "resolved");
        assert_eq!(state["substitution"]["term"]["tag"], "And");
        let bindings = state["substitution"]["term"]["patterns"]
            .as_array()
            .unwrap();
        assert_eq!(bindings.len(), 2);
        assert!(bindings.iter().all(|binding| binding["tag"] == "Equals"));
        assert!(
            bindings
                .iter()
                .all(|binding| binding["second"]["value"] == "resolved")
        );
        assert!(state.get("predicate").is_none());
    }

    #[test]
    fn execute_projects_a_resolved_rewrite_existential_as_a_substitution() {
        let syntax = parse_definition(
            r#"[]
                module TEST
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                  sort SortState{} []
                  symbol initial{}() : SortState{} [constructor{}()]
                  symbol state{}(SortInt{}) : SortState{} [constructor{}()]
                  hooked-symbol eq{}(SortInt{}, SortInt{}) : SortBool{}
                    [function{}(), total{}(), hook{}("INT.eq"), smt-hook{}("=")]
                  axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(initial{}(), \top{SortState{}}()),
                    \exists{SortState{}}(
                      Var'Ques'X:SortInt{},
                      \and{SortState{}}(
                        state{}(Var'Ques'X:SortInt{}),
                        \equals{SortBool{}, SortState{}}(
                          eq{}(Var'Ques'X:SortInt{}, \dv{SortInt{}}("42")),
                          \dv{SortBool{}}("true")
                        )
                      )
                    )
                  ) [label{}("TEST.resolve"), UNIQUE'Unds'ID{}("resolve-rule")]
                endmodule []"#,
        )
        .expect("definition should parse");
        let mut service = RpcService::new(BackendSession::new(syntax, "TEST"));
        let state = encode_kore(&parse_pattern("initial{}()").unwrap()).unwrap();

        let response = request(&mut service, 1, "execute", json!({ "state": state }));

        assert_eq!(response["result"]["reason"], "stuck", "{response:#}");
        assert_eq!(response["result"]["depth"], 1);
        assert_eq!(
            response["result"]["state"]["term"]["term"]["args"][0]["value"],
            "42"
        );
        let substitution = &response["result"]["state"]["substitution"]["term"];
        assert_eq!(substitution["tag"], "Equals");
        assert_eq!(substitution["first"]["name"], "Var'Ques'X");
        assert_eq!(substitution["second"]["value"], "42");
        assert!(response["result"]["state"].get("predicate").is_none());
    }

    #[test]
    fn execute_reports_kequal_ensures_as_substitution() {
        let syntax = parse_definition(
            r#"[]
                module TEST
                  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                  sort SortFoo{} []
                  sort SortKItem{} []
                  sort SortK{} []
                  sort SortState{} []
                  symbol initial{}() : SortState{} [constructor{}()]
                  symbol value{}() : SortFoo{} [constructor{}()]
                  symbol state{}(SortFoo{}) : SortState{} [constructor{}()]
                  symbol dotk{}() : SortK{} [constructor{}()]
                  symbol kseq{}(SortKItem{}, SortK{}) : SortK{}
                    [constructor{}(), injective{}()]
                  hooked-symbol equalK{}(SortK{}, SortK{}) : SortBool{}
                    [function{}(), total{}(), hook{}("KEQUAL.eq")]
                  symbol inj{From, To}(From) : To [sortInjection{}(), injective{}()]
                  axiom{R} \exists{R}(
                    Value:SortKItem{},
                    \equals{SortKItem{}, R}(
                      Value:SortKItem{},
                      inj{SortFoo{}, SortKItem{}}(From:SortFoo{})
                    )
                  ) [subsort{SortFoo{}, SortKItem{}}()]
                  axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(initial{}(), \top{SortState{}}()),
                    \exists{SortState{}}(
                      Var'Ques'Y:SortFoo{},
                      \and{SortState{}}(
                        state{}(Var'Ques'Y:SortFoo{}),
                        \equals{SortBool{}, SortState{}}(
                          equalK{}(
                            kseq{}(
                              inj{SortFoo{}, SortKItem{}}(Var'Ques'Y:SortFoo{}),
                              dotk{}()
                            ),
                            kseq{}(
                              inj{SortFoo{}, SortKItem{}}(value{}()),
                              dotk{}()
                            )
                          ),
                          \dv{SortBool{}}("true")
                        )
                      )
                    )
                  ) [label{}("TEST.resolve-k"), UNIQUE'Unds'ID{}("resolve-k-rule")]
                endmodule []"#,
        )
        .expect("definition should parse");
        let mut service = RpcService::new(BackendSession::new(syntax, "TEST"));
        let state = encode_kore(&parse_pattern("initial{}()").unwrap()).unwrap();

        let response = request(&mut service, 1, "execute", json!({ "state": state }));

        assert_eq!(response["result"]["reason"], "stuck", "{response:#}");
        assert_eq!(response["result"]["depth"], 1);
        assert_eq!(
            response["result"]["state"]["term"]["term"]["args"][0]["name"],
            "value"
        );
        let substitution = &response["result"]["state"]["substitution"]["term"];
        assert_eq!(substitution["tag"], "Equals");
        assert_eq!(substitution["first"]["name"], "Var'Ques'Y");
        assert_eq!(substitution["second"]["name"], "value");
        assert!(response["result"]["state"].get("predicate").is_none());
    }

    #[test]
    fn retains_a_cycle_breaking_equation_outside_the_rpc_substitution() {
        let sort = BackendSort::simple("SortState");
        let x = Variable::new("X", sort.clone());
        let y = Variable::new("Y", sort);
        let constraints = vec![
            Predicate::Equals(Term::variable(y.clone()), Term::variable(x.clone())),
            Predicate::Equals(Term::variable(x.clone()), Term::variable(y.clone())),
        ];

        let (predicates, substitution) = split_constraints(
            &constraints,
            &BTreeSet::from([x.clone(), y.clone()]),
            &SortGraph::default(),
        );

        assert_eq!(
            substitution,
            Substitution::from([(y.clone(), Term::variable(x))])
        );
        assert_eq!(predicates, [constraints[1].clone()]);
    }

    #[test]
    fn externalizes_rule_provenance_and_applies_state_substitutions() {
        let sort = BackendSort::simple("SortState");
        let rule_variable = Variable::new("Rule#X", sort.clone());
        let state_variable = Variable::new("X", sort.clone());
        let rule_substitution =
            Substitution::from([(rule_variable, Term::variable(state_variable.clone()))]);
        let state_substitution =
            Substitution::from([(state_variable, Term::domain_value(sort.clone(), "resolved"))]);

        let pattern =
            externalize_rule_substitution(&rule_substitution, &state_substitution, &sort).unwrap();
        let pattern = encode_kore(&pattern).unwrap();
        assert_eq!(pattern["term"]["first"]["name"], "RuleX");
        assert_eq!(pattern["term"]["second"]["value"], "resolved");
    }

    #[test]
    fn left_associates_rule_substitution_provenance() {
        let sort = BackendSort::simple("SortState");
        let substitution = Substitution::from([
            (
                Variable::new("Rule#A", sort.clone()),
                Term::domain_value(sort.clone(), "a"),
            ),
            (
                Variable::new("Rule#B", sort.clone()),
                Term::domain_value(sort.clone(), "b"),
            ),
            (
                Variable::new("Rule#C", sort.clone()),
                Term::domain_value(sort.clone(), "c"),
            ),
        ]);

        let pattern = externalize_rule_substitution(&substitution, &Substitution::new(), &sort)
            .expect("non-empty rule substitution");
        assert!(matches!(
            &pattern,
            KorePattern::And { arguments, .. }
                if arguments.len() == 2
                    && matches!(&arguments[0], KorePattern::And { arguments, .. }
                        if arguments.len() == 2)
                    && matches!(&arguments[1], KorePattern::Equals { .. })
        ));
    }

    #[test]
    fn get_model_without_a_predicate_reports_unknown() {
        let mut service = service();
        let state = encode_kore(&parse_pattern("state{}()").unwrap()).unwrap();
        let response = request(&mut service, 1, "get-model", json!({ "state": state }));
        assert_eq!(response["result"], json!({ "satisfiable": "Unknown" }));

        // A state with an actual satisfiable predicate still reaches the solver.
        let response = request(
            &mut service,
            2,
            "get-model",
            json!({ "state": trivial_model_state() }),
        );
        assert_eq!(response["result"], json!({ "satisfiable": "Sat" }));
    }

    #[test]
    fn dispatches_simplify_implies_and_get_model() {
        let mut service = service();
        let state = encode_kore(&KorePattern::Application {
            symbol: Symbol {
                name: "state".into(),
                sort_parameters: vec![],
            },
            arguments: vec![],
        })
        .unwrap();
        let model_state = trivial_model_state();

        let simplify = request(
            &mut service,
            1,
            "simplify",
            json!({ "state": state, "haskell-logging": ["Simplify"] }),
        );
        assert_eq!(simplify["result"]["state"]["term"]["tag"], "App");
        assert!(
            !simplify["result"]["haskell-log-entries"]
                .as_array()
                .unwrap()
                .is_empty()
        );

        let implies = request(
            &mut service,
            2,
            "implies",
            json!({
                "antecedent": state,
                "consequent": state,
                "assume-defined": true,
            }),
        );
        assert_eq!(implies["result"]["status"], "valid");
        assert_eq!(
            implies["result"]["condition"]["predicate"]["format"],
            "KORE"
        );

        let model = request(
            &mut service,
            3,
            "get-model",
            json!({ "state": model_state }),
        );
        assert_eq!(model["result"], json!({ "satisfiable": "Sat" }));
    }

    #[test]
    fn simplify_and_execute_budget_asymmetry_is_deliberate() {
        let mut service = budget_policy_service();
        let chain = encode_kore(&parse_pattern("chain0{}()").unwrap()).unwrap();
        let simplify = request(&mut service, 1, "simplify", json!({ "state": chain }));

        // The standalone simplify API is intentionally unbounded for reference parity, while
        // execution uses the shared finite default and continues from the partial result.
        assert!(simplify.get("error").is_none(), "{simplify:#}");
        assert!(simplify["result"]["state"].to_string().contains("done"));

        let initial =
            encode_kore(&parse_pattern(r#"wrap{}(\dv{SortState{}}("value"))"#).unwrap()).unwrap();
        let execute = request(&mut service, 2, "execute", json!({ "state": initial }));
        assert_eq!(execute["result"]["reason"], "branching", "{execute:#}");
        assert_eq!(
            execute["result"]["next-states"].as_array().map(Vec::len),
            Some(2),
            "{execute:#}"
        );

        let configured = request(
            &mut service,
            3,
            "execute",
            json!({
                "state": initial,
                "max-simplification-iterations": 256,
            }),
        );
        assert_eq!(configured["result"]["reason"], "stuck", "{configured:#}");
        assert!(
            configured["result"]["state"].to_string().contains("done"),
            "{configured:#}"
        );
    }

    #[test]
    fn unsupported_hooks_are_runtime_errors_for_execute_and_simplify() {
        let state = encode_kore(&parse_pattern(r#"missing{}(\dv{SortState{}}("value"))"#).unwrap())
            .unwrap();

        for (id, method) in [(1, "execute"), (2, "simplify")] {
            let mut service = unsupported_hook_service();
            let response = request(&mut service, id, method, json!({ "state": state.clone() }));

            assert_eq!(response["error"]["code"], -32002, "{response:#}");
            assert_eq!(
                response["error"]["message"], "Runtime error",
                "{response:#}"
            );
            let error = response["error"]["data"]["error"]
                .as_str()
                .expect("runtime error should contain a textual reason");
            assert!(error.contains("TEST.missing"), "{response:#}");
            assert!(
                response["error"]["data"]["term"].is_object(),
                "{response:#}"
            );
        }
    }

    #[test]
    fn rpc_execute_keeps_console_io_unsupported() {
        let state = encode_kore(
            &parse_pattern(r#"write{}(\dv{SortInt{}}("1"), \dv{SortString{}}("not delivered"))"#)
                .unwrap(),
        )
        .unwrap();
        let mut service = console_hook_service();

        let response = request(&mut service, 1, "execute", json!({ "state": state }));

        assert_eq!(response["error"]["code"], -32002, "{response:#}");
        assert_eq!(
            response["error"]["message"], "Runtime error",
            "{response:#}"
        );
        assert!(
            response["error"]["data"]["error"]
                .as_str()
                .is_some_and(|error| error.contains("unsupported hook 'IO.write'")),
            "{response:#}"
        );
    }

    #[test]
    fn simplify_distinguishes_boolean_terms_from_ml_truth() {
        let mut service = boolean_service();
        let boolean = encode_kore(
            &parse_pattern(r#"\dv{SortBool{}}("true")"#).expect("boolean term should parse"),
        )
        .unwrap();
        let logical =
            encode_kore(&parse_pattern(r#"\top{SortBool{}}()"#).expect("ML truth should parse"))
                .unwrap();

        let boolean = request(&mut service, 1, "simplify", json!({ "state": boolean }));
        let logical = request(&mut service, 2, "simplify", json!({ "state": logical }));

        assert_eq!(boolean["result"]["state"]["term"]["tag"], "DV");
        assert_eq!(boolean["result"]["state"]["term"]["value"], "true");
        assert_eq!(logical["result"]["state"]["term"]["tag"], "Top");
    }

    fn divergent_recursion_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  hooked-symbol intAdd{}(SortInt{}, SortInt{}) : SortInt{}
                    [function{}(), total{}(), hook{}("INT.add")]
                  symbol down{}(SortInt{}) : SortInt{} [function{}()]
                  axiom{R} \implies{R}(
                    \and{R}(\top{R}(), \and{R}(\in{SortInt{}, R}(X0:SortInt{}, N:SortInt{}), \top{R}())),
                    \equals{SortInt{}, R}(
                      down{}(X0:SortInt{}),
                      \and{SortInt{}}(
                        intAdd{}(
                          \dv{SortInt{}}("1"),
                          down{}(intAdd{}(N:SortInt{}, \dv{SortInt{}}("1")))
                        ),
                        \top{SortInt{}}()
                      )
                    )
                  ) [label{}("down")]
                endmodule []"#,
            )
            .unwrap(),
            "TEST",
        ))
    }

    #[test]
    fn stack_exhaustion_is_an_error_response_and_the_connection_keeps_serving() {
        // `down(N) = 1 +Int down(N +Int 1)` never reaches a value, and `simplify` runs without
        // an iteration bound, so only the connection thread's stack ends the request.
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let service = Arc::new(Mutex::new(divergent_recursion_service()));
        let server_service = Arc::clone(&service);
        let worker = thread::spawn(move || {
            let (stream, _) = listener.accept().unwrap();
            serve_connection(stream, server_service).unwrap();
        });

        let state = |source: &str| encode_kore(&parse_pattern(source).unwrap()).unwrap();
        let mut client = TcpStream::connect(address).unwrap();
        let messages = [
            json!({
                "jsonrpc": "2.0",
                "id": 1,
                "method": "simplify",
                "params": { "state": state(r#"down{}(\dv{SortInt{}}("0"))"#) },
            }),
            json!({
                "jsonrpc": "2.0",
                "id": 2,
                "method": "simplify",
                "params": {
                    "state": state(r#"intAdd{}(\dv{SortInt{}}("1"), \dv{SortInt{}}("2"))"#)
                },
            }),
        ];
        for message in messages {
            writeln!(client, "{message}").unwrap();
        }
        // Closing the sending side ends the session, so the answers are read first.
        let mut reader = BufReader::new(client.try_clone().unwrap());
        let mut responses = Vec::new();
        for _ in 0..2 {
            let mut line = String::new();
            reader.read_line(&mut line).unwrap();
            responses.push(serde_json::from_str::<Value>(&line).unwrap());
        }
        client.shutdown(Shutdown::Write).unwrap();
        let mut rest = String::new();
        reader.read_to_string(&mut rest).unwrap();
        worker.join().unwrap();

        assert!(rest.is_empty(), "{rest}");
        assert_eq!(responses[0]["id"], 1);
        assert_eq!(responses[0]["error"]["code"], -32002, "{:#}", responses[0]);
        assert_eq!(
            responses[0]["error"]["data"]["error"],
            SimplificationError::StackExhausted.to_string(),
            "{:#}",
            responses[0]
        );
        assert_eq!(responses[1]["id"], 2);
        assert_eq!(
            responses[1]["result"]["state"]["term"]["value"], "3",
            "{:#}",
            responses[1]
        );
    }

    #[test]
    fn standalone_cancel_with_a_scalar_id_is_consumed_without_a_response() {
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let service = Arc::new(Mutex::new(service()));
        let server_service = Arc::clone(&service);
        let worker = thread::spawn(move || {
            let (stream, _) = listener.accept().unwrap();
            serve_connection(stream, server_service).unwrap();
        });

        let mut client = TcpStream::connect(address).unwrap();
        let messages = [
            json!({ "jsonrpc": "2.0", "id": "swallowed-cancel", "method": "cancel" }),
            json!({ "jsonrpc": "2.0", "id": 1, "method": "missing" }),
            json!({
                "jsonrpc": "2.0",
                "id": 2,
                "method": "get-model",
                "params": { "state": trivial_model_state() },
            }),
        ];
        for message in messages {
            writeln!(client, "{message}").unwrap();
        }
        // Closing the sending side ends the session, so the answers are read first.
        let mut reader = BufReader::new(client.try_clone().unwrap());
        let mut responses = Vec::new();
        for _ in 0..2 {
            let mut line = String::new();
            reader.read_line(&mut line).unwrap();
            responses.push(serde_json::from_str::<Value>(&line).unwrap());
        }
        client.shutdown(Shutdown::Write).unwrap();
        let mut rest = String::new();
        reader.read_to_string(&mut rest).unwrap();
        worker.join().unwrap();

        assert!(
            rest.is_empty(),
            "a standalone cancel must not receive a response even when it has an id: {rest}"
        );
        assert_eq!(responses[0]["error"]["code"], -32601);
        assert_eq!(responses[1]["result"]["satisfiable"], "Sat");
    }

    /// A hang detector, not a timing assertion: a wedged server fails the test instead of
    /// blocking the suite.
    const WATCHDOG: Duration = Duration::from_secs(60);

    fn looping_service() -> RpcService {
        let definition = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    wrap{}(X:SortS{})
                ) [label{}("loop"), UNIQUE'Unds'ID{}("loop")]
            endmodule []"#,
        )
        .unwrap();
        RpcService::new(BackendSession::new(definition, "MAIN"))
    }

    fn divergent_execute() -> Value {
        let state =
            encode_kore(&parse_pattern(r#"wrap{}(\dv{SortS{}}("zero"))"#).unwrap()).unwrap();
        json!({
            "jsonrpc": "2.0",
            "id": "divergent",
            "method": "execute",
            "params": { "state": state },
        })
    }

    /// Accepts `connections` connections on one shared service, each served on its own thread;
    /// every server thread reports its result on the returned channel.
    fn spawn_server(
        service: RpcService,
        connections: usize,
    ) -> (std::net::SocketAddr, mpsc::Receiver<Result<(), String>>) {
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let service = Arc::new(Mutex::new(service));
        let (done, finished) = mpsc::channel();
        thread::spawn(move || {
            for _ in 0..connections {
                let (stream, _) = listener.accept().unwrap();
                let service = Arc::clone(&service);
                let done = done.clone();
                thread::spawn(move || {
                    let result = serve_connection(stream, service).map_err(|e| e.to_string());
                    let _ = done.send(result);
                });
            }
        });
        (address, finished)
    }

    /// A second connection on the same service is answered, which needs the service lock the
    /// first connection's divergent request held.
    fn assert_second_connection_is_served(address: std::net::SocketAddr) {
        let mut client = TcpStream::connect(address).unwrap();
        client.set_read_timeout(Some(WATCHDOG)).unwrap();
        writeln!(
            client,
            "{}",
            json!({ "jsonrpc": "2.0", "id": 9, "method": "missing" })
        )
        .unwrap();
        let mut line = String::new();
        BufReader::new(client.try_clone().unwrap())
            .read_line(&mut line)
            .expect("the second connection must be served once the first one has ended");
        let response: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(response["id"], 9);
        assert_eq!(response["error"]["code"], -32601);
    }

    #[test]
    fn closing_a_connection_cancels_its_divergent_request() {
        let (address, finished) = spawn_server(looping_service(), 2);

        let mut client = TcpStream::connect(address).unwrap();
        writeln!(client, "{}", divergent_execute()).unwrap();
        thread::sleep(Duration::from_millis(50));
        drop(client);

        finished
            .recv_timeout(WATCHDOG)
            .expect("the closed connection's session must end")
            .unwrap();
        assert_second_connection_is_served(address);
    }

    #[test]
    fn half_closing_a_connection_cancels_its_divergent_request() {
        let (address, finished) = spawn_server(looping_service(), 2);

        let mut client = TcpStream::connect(address).unwrap();
        client.set_read_timeout(Some(WATCHDOG)).unwrap();
        writeln!(client, "{}", divergent_execute()).unwrap();
        thread::sleep(Duration::from_millis(50));
        client.shutdown(Shutdown::Write).unwrap();

        let mut answer = String::new();
        client
            .read_to_string(&mut answer)
            .expect("the server must close the connection after its session ends");
        assert!(
            answer.is_empty(),
            "a request cancelled by the end of its session is not answered: {answer}"
        );
        finished
            .recv_timeout(WATCHDOG)
            .expect("the half-closed connection's session must end")
            .unwrap();
        assert_second_connection_is_served(address);
    }

    #[test]
    fn accepted_connections_carry_tcp_keepalive_and_user_timeout() {
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let client = TcpStream::connect(address).unwrap();
        let (stream, _) = listener.accept().unwrap();
        // A duplicate descriptor of the served socket, to read its options back.
        let served = stream.try_clone().unwrap();
        let server = thread::spawn(move || {
            serve_connection(stream, Arc::new(Mutex::new(service()))).unwrap();
        });

        let mut client = client;
        client.set_read_timeout(Some(WATCHDOG)).unwrap();
        writeln!(
            client,
            "{}",
            json!({ "jsonrpc": "2.0", "id": 1, "method": "missing" })
        )
        .unwrap();
        let mut line = String::new();
        BufReader::new(client.try_clone().unwrap())
            .read_line(&mut line)
            .unwrap();

        let socket = socket2::SockRef::from(&served);
        assert!(socket.keepalive().unwrap());
        assert_eq!(socket.tcp_keepalive_time().unwrap(), KEEPALIVE_IDLE);
        assert_eq!(socket.tcp_keepalive_interval().unwrap(), KEEPALIVE_INTERVAL);
        assert_eq!(socket.tcp_keepalive_retries().unwrap(), KEEPALIVE_RETRIES);
        #[cfg(any(target_os = "linux", target_os = "android"))]
        assert_eq!(
            socket.tcp_user_timeout().unwrap(),
            Some(UNACKNOWLEDGED_DATA_TIMEOUT)
        );

        drop(client);
        server.join().unwrap();
    }

    #[test]
    fn serves_a_complete_request_without_waiting_for_a_newline_or_eof() {
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let service = Arc::new(Mutex::new(service()));
        let server_service = Arc::clone(&service);
        let worker = thread::spawn(move || {
            let (stream, _) = listener.accept().unwrap();
            serve_connection(stream, server_service).unwrap();
        });

        let mut client = TcpStream::connect(address).unwrap();
        let mut response = BufReader::new(client.try_clone().unwrap());
        write!(
            client,
            "{}",
            json!({ "jsonrpc": "2.0", "id": 7, "method": "missing" })
        )
        .unwrap();
        client.flush().unwrap();

        let mut line = String::new();
        response.read_line(&mut line).unwrap();
        let response: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(response["id"], 7);
        assert_eq!(response["error"]["code"], -32601);

        client.shutdown(Shutdown::Write).unwrap();
        worker.join().unwrap();
    }

    #[test]
    fn standalone_cancel_interrupts_the_active_request_and_keeps_the_connection_alive() {
        let definition = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    wrap{}(X:SortS{})
                ) [label{}("loop"), UNIQUE'Unds'ID{}("loop")]
            endmodule []"#,
        )
        .unwrap();
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let service = Arc::new(Mutex::new(RpcService::new(BackendSession::new(
            definition, "MAIN",
        ))));
        let server_service = Arc::clone(&service);
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().unwrap();
            serve_connection(stream, server_service).unwrap();
        });

        let mut client = TcpStream::connect(address).unwrap();
        let mut responses = BufReader::new(client.try_clone().unwrap());
        let state =
            encode_kore(&parse_pattern(r#"wrap{}(\dv{SortS{}}("zero"))"#).unwrap()).unwrap();
        writeln!(
            client,
            "{}",
            json!({
                "jsonrpc": "2.0",
                "id": "slow-request",
                "method": "execute",
                "params": { "state": state },
            })
        )
        .unwrap();
        thread::sleep(Duration::from_millis(10));
        writeln!(
            client,
            "{}",
            json!({ "jsonrpc": "2.0", "id": "cancel-command", "method": "cancel" })
        )
        .unwrap();

        let mut line = String::new();
        responses.read_line(&mut line).unwrap();
        let cancelled: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(
            cancelled,
            json!({
                "jsonrpc": "2.0",
                "id": "slow-request",
                "error": {
                    "code": -32000,
                    "message": "Request cancelled",
                    "data": null,
                },
            })
        );

        writeln!(
            client,
            "{}",
            json!({ "jsonrpc": "2.0", "id": 8, "method": "missing" })
        )
        .unwrap();
        line.clear();
        responses.read_line(&mut line).unwrap();
        let next: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(next["id"], 8);
        assert_eq!(next["error"]["code"], -32601);

        client.shutdown(Shutdown::Write).unwrap();
        server.join().unwrap();
    }

    #[test]
    fn cancelling_a_batch_yields_a_batch_shaped_cancellation_response() {
        let definition = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{}
                    [function{}(), total{}(), injective{}(), no-evaluators{}()]
                axiom{} \rewrites{SortS{}}(
                    \and{SortS{}}(wrap{}(X:SortS{}), \top{SortS{}}()),
                    wrap{}(X:SortS{})
                ) [label{}("loop"), UNIQUE'Unds'ID{}("loop")]
            endmodule []"#,
        )
        .unwrap();
        let listener = TcpListener::bind(("127.0.0.1", 0)).unwrap();
        let address = listener.local_addr().unwrap();
        let service = Arc::new(Mutex::new(RpcService::new(BackendSession::new(
            definition, "MAIN",
        ))));
        let server_service = Arc::clone(&service);
        let server = thread::spawn(move || {
            let (stream, _) = listener.accept().unwrap();
            serve_connection(stream, server_service).unwrap();
        });

        let mut client = TcpStream::connect(address).unwrap();
        let mut responses = BufReader::new(client.try_clone().unwrap());
        let state =
            encode_kore(&parse_pattern(r#"wrap{}(\dv{SortS{}}("zero"))"#).unwrap()).unwrap();
        writeln!(
            client,
            "{}",
            json!([{
                "jsonrpc": "2.0",
                "id": "slow-batch-request",
                "method": "execute",
                "params": { "state": state },
            }])
        )
        .unwrap();
        thread::sleep(Duration::from_millis(10));
        writeln!(
            client,
            "{}",
            json!({ "jsonrpc": "2.0", "id": "cancel-command", "method": "cancel" })
        )
        .unwrap();

        let mut line = String::new();
        responses.read_line(&mut line).unwrap();
        let cancelled: Value = serde_json::from_str(&line).unwrap();
        assert_eq!(
            cancelled,
            json!([{
                "jsonrpc": "2.0",
                "id": "slow-batch-request",
                "error": {
                    "code": -32000,
                    "message": "Request cancelled",
                    "data": null,
                },
            }])
        );

        client.shutdown(Shutdown::Write).unwrap();
        server.join().unwrap();
    }

    fn request(service: &mut RpcService, id: u64, method: &str, params: Value) -> Value {
        request_with_id(service, Value::from(id), method, params)
    }

    fn request_with_id(service: &mut RpcService, id: Value, method: &str, params: Value) -> Value {
        let request = json!({
            "jsonrpc": "2.0",
            "id": id,
            "method": method,
            "params": params,
        });
        serde_json::from_str(&service.handle_line(&request.to_string()).unwrap()).unwrap()
    }

    fn trivial_model_state() -> Value {
        let sort = k_rust::kore::ast::Sort::Application {
            name: "SortState".into(),
            arguments: vec![],
        };
        let state = || KorePattern::Application {
            symbol: Symbol {
                name: "state".into(),
                sort_parameters: vec![],
            },
            arguments: vec![],
        };
        encode_kore(&KorePattern::Equals {
            operand_sort: sort.clone(),
            result_sort: sort,
            left: Box::new(state()),
            right: Box::new(state()),
        })
        .unwrap()
    }
}
