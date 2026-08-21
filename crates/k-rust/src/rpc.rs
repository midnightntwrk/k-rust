//! Stateful KORE JSON-RPC 2.0 dispatch and raw TCP transport.

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

use k_rust::kore::{
    ast::{Pattern as KorePattern, Sort as KoreSort, Variable as KoreVariable},
    json as kore_json,
    parser::parse_module,
};
use k_rust_backend::{
    cancellation::{CancellationToken, cancellation_requested},
    definition::{BackendDefinition, DefinitionError},
    externalize,
    implication::{
        ImplicationCondition, ImplicationError, ImplicationFailure, ImplicationResult,
        ImplicationStatus, check_implication_with_existentials,
    },
    rewrite::{
        AppliedRule, ExecutionBranchMode, ExecutionMode, ExecutionOptions, HaltReason, Pattern,
        TraceKind, execute_with_solver, substitute_predicates,
    },
    rule::{Predicate, RulePatternError},
    session::{BackendSession, SessionError},
    simplify::{
        SimplificationError, SimplificationOptions, simplify_and_decide_predicate_with_solver,
        simplify_pattern_with_solver,
    },
    smt::{ModelResult, SmtError, SmtSolver, Z3Options, Z3Solver},
    substitution::{Substitution, extract_substitution, substitute},
    term::{Sort as BackendSort, Term, Variable},
};
use serde::Deserialize;
use serde_json::{Map, Value, json};

const JSON_RPC_VERSION: &str = "2.0";
const CONNECTION_STACK_SIZE: usize = 64 * 1024 * 1024;
const REQUEST_PENDING: u8 = 0;
const REQUEST_CANCELLED: u8 = 1;
const REQUEST_COMPLETED: u8 = 2;

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
    session: BackendSession,
    smt_options: Z3Options,
}

#[derive(Debug)]
struct RpcFault {
    code: i64,
    message: String,
    data: Option<Value>,
}

#[derive(Debug)]
struct KoreJson(KorePattern);

impl<'de> Deserialize<'de> for KoreJson {
    fn deserialize<D: serde::Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        let value = Value::deserialize(deserializer)?;
        let source = serde_json::to_string(&value).map_err(serde::de::Error::custom)?;
        kore_json::from_str_unbounded(&source)
            .map(Self)
            .map_err(serde::de::Error::custom)
    }
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
struct ExecuteParams {
    state: KoreJson,
    #[serde(default)]
    max_depth: Option<u64>,
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
#[serde(rename_all = "kebab-case")]
struct SimplifyParams {
    state: KoreJson,
    #[serde(default)]
    module: Option<String>,
    #[serde(default)]
    booster_only: bool,
    #[serde(default)]
    haskell_logging: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
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
#[serde(rename_all = "kebab-case")]
struct AddModuleParams {
    module: String,
    #[serde(default)]
    name_as_id: bool,
    #[serde(default)]
    haskell_logging: Vec<String>,
}

#[derive(Debug, Deserialize)]
#[serde(rename_all = "kebab-case")]
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

    fn cancel_unsupported_in_batch() -> Self {
        Self {
            code: -32001,
            message: "Cancel request unsupported in batch mode".into(),
            data: Some(Value::Null),
        }
    }

    fn invalid_request(data: Option<Value>) -> Self {
        Self {
            code: -32600,
            message: "Invalid Request".into(),
            data,
        }
    }

    fn invalid_params(data: Value) -> Self {
        Self {
            code: -32602,
            message: "Invalid params".into(),
            data: Some(data),
        }
    }

    fn backend(message: impl Into<String>) -> Self {
        Self {
            code: 1,
            message: message.into(),
            data: None,
        }
    }

    fn pattern(error: impl ToString) -> Self {
        Self {
            code: 2,
            message: "Could not verify pattern".into(),
            data: Some(Value::String(error.to_string())),
        }
    }

    fn implication(error: impl Into<String>, context: Vec<String>) -> Self {
        Self {
            code: 4,
            message: "Implication check error".into(),
            data: Some(json!({
                "context": context,
                "error": error.into(),
            })),
        }
    }

    fn module(module: &str, _error: impl ToString) -> Self {
        Self {
            code: 3,
            message: "Could not find module".into(),
            data: Some(Value::String(module.into())),
        }
    }

    fn invalid_module(module: &str) -> Self {
        Self {
            code: 8,
            message: "Invalid module".into(),
            data: Some(json!({ "error": format!("Module {module} not found.") })),
        }
    }

    fn duplicate_module_name(module: String) -> Self {
        Self {
            code: 9,
            message: "Duplicate module name".into(),
            data: Some(Value::String(module)),
        }
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

impl RpcService {
    #[cfg(test)]
    pub(super) fn new(session: BackendSession) -> Self {
        Self::with_smt_options(session, Z3Options::default())
    }

    pub(super) fn with_smt_options(session: BackendSession, smt_options: Z3Options) -> Self {
        Self {
            session,
            smt_options,
        }
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
                Some(RpcFault::invalid_request(None).into_value(Value::Null))
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
        let params = object.get("params").cloned().unwrap_or_else(|| json!({}));
        let result = self.dispatch(method, params.clone());
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
            "cancel" => Err(RpcFault::cancel_unsupported_in_batch()),
            _ => Err(RpcFault {
                code: -32601,
                message: "Method not found".into(),
                data: None,
            }),
        };
        if cancellation_requested() {
            Err(RpcFault::cancelled())
        } else {
            result.map(|mut result| {
                attach_legacy_log_entries(method, &requested_logs, &mut result);
                result
            })
        }
    }

    fn definition(&mut self, module: Option<&str>) -> Result<Arc<BackendDefinition>, RpcFault> {
        let requested = module.unwrap_or(self.session.default_module()).to_owned();
        self.session
            .definition(module)
            .map_err(|error| RpcFault::module(&requested, error))
    }

    fn execute(&mut self, params: ExecuteParams) -> Result<Value, RpcFault> {
        let ExecuteParams {
            state,
            max_depth,
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
        let definition = self.definition(module.as_deref())?;
        let syntax = state.0;
        let initial = definition
            .internalize_pattern(&syntax, &[])
            .map_err(|error| pattern_fault(error, &syntax))?;
        let configuration_variables = pattern_variables(&initial);
        let solver = solver(&definition, self.smt_options)?;
        let result = execute_with_solver(
            &definition,
            initial,
            ExecutionOptions {
                max_depth: max_depth.unwrap_or(u64::MAX),
                mode: ExecutionMode::All,
                branch_mode: ExecutionBranchMode::StopAtBranch,
                cut_point_rules: cut_point_rules.into_iter().collect(),
                terminal_rules: terminal_rules.into_iter().collect(),
                step_timeout: step_timeout.map(Duration::from_millis),
                moving_average_timeout: moving_average_step_timeout,
                assume_initial_defined: assume_state_defined,
                ..ExecutionOptions::default()
            },
            &solver,
        );
        let leaf = result
            .leaves
            .into_iter()
            .next()
            .ok_or_else(|| RpcFault::backend("execution produced no result"))?;
        let mut output = Map::new();
        let (reason, next_states, rule) = match &leaf.halt_reason {
            HaltReason::Cancelled => return Err(RpcFault::cancelled()),
            HaltReason::Stuck => ("stuck", None, None),
            HaltReason::Trivial | HaltReason::Vacuous => ("vacuous", None, None),
            HaltReason::DepthBound => ("depth-bound", None, None),
            HaltReason::BreadthBound => ("aborted", None, None),
            HaltReason::Timeout(_) => ("timeout", None, None),
            HaltReason::Indeterminate(_) | HaltReason::Simplification(_) => ("aborted", None, None),
            HaltReason::Branch {
                branches,
                remainder,
            } => {
                let mut next_states = branches
                    .iter()
                    .rev()
                    .map(|applied| {
                        execute_applied_state(&definition, applied, &configuration_variables)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                if let Some(remainder) = remainder {
                    next_states.push(execute_state(
                        &definition,
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
                            execute_state(&definition, &applied.pattern, &configuration_variables)
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                Some(rule.clone()),
            ),
            HaltReason::TerminalRule { rule } => ("terminal-rule", None, Some(rule.clone())),
        };
        output.insert("reason".into(), Value::String(reason.into()));
        output.insert("depth".into(), Value::from(leaf.depth));
        if let Some(rule) = rule {
            output.insert("rule".into(), Value::String(rule));
        }
        output.insert(
            "state".into(),
            execute_state(&definition, &leaf.pattern, &configuration_variables)?,
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
    }

    fn simplify(&mut self, params: SimplifyParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        let _haskell_logging = params.haskell_logging;
        let definition = self.definition(params.module.as_deref())?;
        let syntax = params.state.0;
        let solver = solver(&definition, self.smt_options)?;
        match definition.internalize_pattern(&syntax, &[]) {
            Ok(pattern) => {
                let simplified = simplify_pattern_with_solver(
                    &definition,
                    &pattern,
                    SimplificationOptions::default(),
                    &solver,
                )
                .map_err(|error| simplify_fault(error, &pattern.term.sort()))?;
                return Ok(json!({
                    "state": encode_kore(&externalize::constrained_pattern(&simplified))?
                }));
            }
            Err(DefinitionError::RulePattern(RulePatternError::MissingTerm)) => {}
            Err(error) => return Err(pattern_fault(error, &syntax)),
        }
        let (predicate, result_sort) = definition
            .internalize_predicate(&syntax, &[])
            .map_err(|error| pattern_fault(error, &syntax))?;
        let simplified = simplify_and_decide_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &solver,
        )
        .map_err(|error| simplify_fault(error, &result_sort))?;
        Ok(json!({ "state": encode_kore(&externalize::ml_pattern(&simplified, &result_sort))? }))
    }

    fn add_module(&mut self, params: AddModuleParams) -> Result<Value, RpcFault> {
        let _haskell_logging = params.haskell_logging;
        let module = parse_module(&params.module)
            .map_err(|error| RpcFault::backend(format!("could not parse module: {error}")))?;
        let id = self
            .session
            .add_module(&params.module, module, params.name_as_id)
            .map_err(|error| match error {
                SessionError::Definition(DefinitionError::NoSuchModule(module)) => {
                    RpcFault::invalid_module(&module)
                }
                SessionError::DuplicateModuleName(module) => {
                    RpcFault::duplicate_module_name(module)
                }
                error => RpcFault::backend(format!("could not add module: {error}")),
            })?;
        Ok(json!({ "module": id }))
    }

    fn get_model(&mut self, params: GetModelParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        let _haskell_logging = params.haskell_logging;
        let definition = self.definition(params.module.as_deref())?;
        let syntax = params.state.0;
        let Some((predicate, result_sort)) = definition
            .internalize_model_predicate(&syntax, &[])
            .map_err(|error| pattern_fault(error, &syntax))?
        else {
            return Ok(json!({ "satisfiable": "Unknown" }));
        };
        let solver = solver(&definition, self.smt_options)?;
        match solver
            .get_model(&[predicate], &Substitution::new())
            .map_err(|error| RpcFault::backend(format!("could not obtain model: {error:?}")))?
        {
            ModelResult::Sat(substitution) => {
                let mut result = json!({ "satisfiable": "Sat" });
                if let Some(substitution) = super::model_substitution(&substitution, &result_sort) {
                    result["substitution"] = encode_kore(&substitution)?;
                }
                Ok(result)
            }
            ModelResult::Unsat => Ok(json!({ "satisfiable": "Unsat" })),
            ModelResult::Unknown(_) => Ok(json!({ "satisfiable": "Unknown" })),
        }
    }

    fn implies(&mut self, params: ImpliesParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        // The reference proxy uses `assume-defined` as a backend-routing hint. The unified Rust
        // backend already runs the in-process implication path it selects.
        let _assume_defined = params.assume_defined;
        let _haskell_logging = params.haskell_logging;
        let definition = self.definition(params.module.as_deref())?;
        let antecedent = params.antecedent.0;
        let consequent = params.consequent.0;
        definition
            .validate_implication_pattern(&antecedent)
            .map_err(|error| implication_pattern_fault(error, &antecedent))?;
        definition
            .validate_implication_pattern(&consequent)
            .map_err(|error| implication_pattern_fault(error, &consequent))?;
        validate_singleton_implication_patterns(&antecedent, &consequent)?;
        validate_implication_variable_capture(&antecedent, &consequent)?;
        validate_implication_sorts(&antecedent, &consequent)?;
        let sort_variables = super::implication_sort_variables(&antecedent, &consequent);
        if let Some(result) = special_implication_result(&antecedent, &consequent) {
            let (_, result_sort) = definition
                .internalize_predicate(&antecedent, &sort_variables)
                .map_err(RpcFault::pattern)?;
            return implication_result(&antecedent, &consequent, &result_sort, result);
        }
        let (antecedent_pattern, antecedent_existentials) = definition
            .internalize_implication_pattern(&antecedent, &sort_variables)
            .map_err(RpcFault::pattern)?;
        let result_sort = antecedent_pattern.term.sort();
        if matches!(super::strip_exists(&consequent), KorePattern::Not { .. }) {
            let result = ImplicationResult {
                status: ImplicationStatus::Invalid,
                condition: None,
                failure: None,
            };
            let antecedent = normalized_implication_syntax(&antecedent, &antecedent_pattern);
            return implication_result(&antecedent, &consequent, &result_sort, result);
        }
        let (consequent_pattern, consequent_existentials) = definition
            .internalize_implication_pattern(&consequent, &sort_variables)
            .map_err(RpcFault::pattern)?;
        if result_sort != consequent_pattern.term.sort() {
            return Err(RpcFault::pattern("antecedent and consequent sorts differ"));
        }
        let solver = solver(&definition, self.smt_options)?;
        let result = check_implication_with_existentials(
            &definition,
            &antecedent_pattern,
            &antecedent_existentials,
            &consequent_pattern,
            &consequent_existentials,
            &solver,
        )
        .map_err(|error| {
            implication_backend_fault(error, &antecedent, &consequent, &consequent_existentials)
        })?;
        let vacuous_antecedent = result.status == ImplicationStatus::Valid
            && result.condition.as_ref().is_some_and(|condition| {
                condition.predicates.as_slice() == [Predicate::False]
                    && condition.substitution.is_empty()
            });
        let antecedent = if vacuous_antecedent {
            antecedent
        } else {
            normalized_implication_syntax(&antecedent, &antecedent_pattern)
        };
        let consequent = if vacuous_antecedent {
            consequent
        } else {
            normalized_implication_syntax(&consequent, &consequent_pattern)
        };
        implication_result(&antecedent, &consequent, &result_sort, result)
    }
}

fn simplify_fault(error: SimplificationError, result_sort: &BackendSort) -> RpcFault {
    let SimplificationError::SmtPredicate { predicate, error } = error else {
        return RpcFault::backend(format!("could not simplify pattern: {error:?}"));
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
        return RpcFault::backend("could not encode the predicate rejected by SMT");
    };
    RpcFault {
        code: 5,
        message: "Smt solver error".into(),
        data: Some(json!({ "term": term, "error": reason })),
    }
}

fn contains_integer_power_application(pattern: &KorePattern) -> bool {
    match pattern {
        KorePattern::Application { symbol, arguments }
        | KorePattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            symbol.name == "Lbl'UndsXor-'Int'Unds'"
                || arguments.iter().any(contains_integer_power_application)
        }
        KorePattern::And { arguments, .. } | KorePattern::Or { arguments, .. } => {
            arguments.iter().any(contains_integer_power_application)
        }
        KorePattern::Not { argument, .. }
        | KorePattern::Next { argument, .. }
        | KorePattern::Ceil { argument, .. }
        | KorePattern::Floor { argument, .. } => contains_integer_power_application(argument),
        KorePattern::Implies { left, right, .. }
        | KorePattern::Iff { left, right, .. }
        | KorePattern::Rewrites { left, right, .. }
        | KorePattern::Equals { left, right, .. }
        | KorePattern::In { left, right, .. } => {
            contains_integer_power_application(left) || contains_integer_power_application(right)
        }
        KorePattern::Exists { body, .. }
        | KorePattern::Forall { body, .. }
        | KorePattern::Mu { body, .. }
        | KorePattern::Nu { body, .. } => contains_integer_power_application(body),
        KorePattern::String(_)
        | KorePattern::Variable(_)
        | KorePattern::Top { .. }
        | KorePattern::Bottom { .. }
        | KorePattern::DomainValue { .. } => false,
    }
}

fn implication_pattern_fault(error: DefinitionError, pattern: &KorePattern) -> RpcFault {
    let DefinitionError::MacroOrAliasInImplication(name) = error else {
        return RpcFault::pattern(error);
    };
    let context = macro_or_alias_context(pattern, &name)
        .unwrap_or_else(|| vec![format!("symbol or alias '{name}' (<unknown location>)")]);
    RpcFault {
        code: 2,
        message: "Could not verify pattern".into(),
        data: Some(json!([{
            "context": context,
            "error": "A symbol cannot be an alias or a macro",
        }])),
    }
}

fn pattern_fault(error: DefinitionError, pattern: &KorePattern) -> RpcFault {
    let detail = match &error {
        DefinitionError::WrongSymbolArity {
            symbol,
            expected,
            actual,
        } => find_application(pattern, symbol, Some(*actual), None, None).map(|(term, _)| {
            (
                term,
                format!(
                    "Inconsistent pattern. Symbol '{symbol}' expected {expected} arguments but got {actual}"
                ),
            )
        }),
        DefinitionError::IncorrectArgumentSort {
            symbol,
            index,
            expected,
            actual,
        } => {
            let actual_sort = externalize::sort(actual).to_string();
            find_application(
                pattern,
                symbol,
                None,
                Some((*index, actual_sort.as_str())),
                None,
            )
                .and_then(|(_, arguments)| arguments.get(*index))
                .map(|term| {
                    (
                        term,
                        format!(
                            "Incorrect sort: expected {} but got {actual_sort}",
                            externalize::sort(expected)
                        ),
                    )
                })
        }
        DefinitionError::NotSubsort { source, target } => {
            let source = externalize::sort(source).to_string();
            let target = externalize::sort(target).to_string();
            find_application(
                pattern,
                "inj",
                Some(1),
                None,
                Some((source.as_str(), target.as_str())),
            )
            .map(|(term, _)| {
                (
                    term,
                    format!("{source} is not a subsort of {target}"),
                )
            })
        }
        _ => None,
    };
    let Some((term, message)) = detail else {
        return RpcFault::pattern(error);
    };
    let Ok(term) = encode_kore(term) else {
        return RpcFault::pattern(error);
    };
    RpcFault {
        code: 2,
        message: "Could not verify pattern".into(),
        data: Some(json!([{ "term": term, "error": message }])),
    }
}

fn find_application<'a>(
    pattern: &'a KorePattern,
    symbol_name: &str,
    actual_arity: Option<usize>,
    argument_sort: Option<(usize, &str)>,
    sort_parameters: Option<(&str, &str)>,
) -> Option<(&'a KorePattern, &'a [KorePattern])> {
    let nested = match pattern {
        KorePattern::Application { arguments, .. }
        | KorePattern::AssociativeApplication { arguments, .. }
        | KorePattern::And { arguments, .. }
        | KorePattern::Or { arguments, .. } => arguments.iter().find_map(|argument| {
            find_application(
                argument,
                symbol_name,
                actual_arity,
                argument_sort,
                sort_parameters,
            )
        }),
        KorePattern::Not { argument, .. }
        | KorePattern::Next { argument, .. }
        | KorePattern::Ceil { argument, .. }
        | KorePattern::Floor { argument, .. } => find_application(
            argument,
            symbol_name,
            actual_arity,
            argument_sort,
            sort_parameters,
        ),
        KorePattern::Implies { left, right, .. }
        | KorePattern::Iff { left, right, .. }
        | KorePattern::Rewrites { left, right, .. }
        | KorePattern::Equals { left, right, .. }
        | KorePattern::In { left, right, .. } => find_application(
            left,
            symbol_name,
            actual_arity,
            argument_sort,
            sort_parameters,
        )
        .or_else(|| {
            find_application(
                right,
                symbol_name,
                actual_arity,
                argument_sort,
                sort_parameters,
            )
        }),
        KorePattern::Exists { body, .. }
        | KorePattern::Forall { body, .. }
        | KorePattern::Mu { body, .. }
        | KorePattern::Nu { body, .. } => find_application(
            body,
            symbol_name,
            actual_arity,
            argument_sort,
            sort_parameters,
        ),
        KorePattern::String(_)
        | KorePattern::Variable(_)
        | KorePattern::Top { .. }
        | KorePattern::Bottom { .. }
        | KorePattern::DomainValue { .. } => None,
    };
    if nested.is_some() {
        return nested;
    }
    let (symbol, arguments) = match pattern {
        KorePattern::Application { symbol, arguments }
        | KorePattern::AssociativeApplication {
            symbol, arguments, ..
        } => (symbol, arguments.as_slice()),
        _ => return None,
    };
    if symbol.name != symbol_name || actual_arity.is_some_and(|arity| arguments.len() != arity) {
        return None;
    }
    if let Some((source, target)) = sort_parameters
        && !matches!(
            symbol.sort_parameters.as_slice(),
            [actual_source, actual_target]
                if actual_source.to_string() == source && actual_target.to_string() == target
        )
    {
        return None;
    }
    if let Some((index, expected_sort)) = argument_sort
        && arguments
            .get(index)
            .and_then(explicit_pattern_sort)
            .is_some_and(|sort| sort.to_string() != expected_sort)
    {
        return None;
    }
    Some((pattern, arguments))
}

fn explicit_pattern_sort(pattern: &KorePattern) -> Option<&KoreSort> {
    match pattern {
        KorePattern::Variable(variable) => Some(&variable.sort),
        KorePattern::DomainValue { sort, .. }
        | KorePattern::Top { sort }
        | KorePattern::Bottom { sort }
        | KorePattern::Not { sort, .. }
        | KorePattern::Next { sort, .. }
        | KorePattern::And { sort, .. }
        | KorePattern::Or { sort, .. }
        | KorePattern::Rewrites { sort, .. }
        | KorePattern::Implies { sort, .. }
        | KorePattern::Iff { sort, .. }
        | KorePattern::Exists { sort, .. }
        | KorePattern::Forall { sort, .. } => Some(sort),
        KorePattern::Ceil { result_sort, .. }
        | KorePattern::Floor { result_sort, .. }
        | KorePattern::Equals { result_sort, .. }
        | KorePattern::In { result_sort, .. } => Some(result_sort),
        KorePattern::Mu { variable, .. } | KorePattern::Nu { variable, .. } => Some(&variable.sort),
        KorePattern::Application { .. }
        | KorePattern::AssociativeApplication { .. }
        | KorePattern::String(_) => None,
    }
}

fn macro_or_alias_context(pattern: &KorePattern, name: &str) -> Option<Vec<String>> {
    let mut context = match pattern {
        KorePattern::Application { symbol, arguments }
        | KorePattern::AssociativeApplication {
            symbol, arguments, ..
        } => {
            if symbol.name == name {
                return Some(vec![format!(
                    "symbol or alias '{name}' (<unknown location>)"
                )]);
            }
            arguments
                .iter()
                .find_map(|argument| macro_or_alias_context(argument, name))?
        }
        KorePattern::And { arguments, .. } | KorePattern::Or { arguments, .. } => arguments
            .iter()
            .find_map(|argument| macro_or_alias_context(argument, name))?,
        KorePattern::Not { argument, .. }
        | KorePattern::Next { argument, .. }
        | KorePattern::Ceil { argument, .. }
        | KorePattern::Floor { argument, .. } => macro_or_alias_context(argument, name)?,
        KorePattern::Implies { left, right, .. }
        | KorePattern::Iff { left, right, .. }
        | KorePattern::Rewrites { left, right, .. }
        | KorePattern::Equals { left, right, .. }
        | KorePattern::In { left, right, .. } => {
            macro_or_alias_context(left, name).or_else(|| macro_or_alias_context(right, name))?
        }
        KorePattern::Exists { body, .. }
        | KorePattern::Forall { body, .. }
        | KorePattern::Mu { body, .. }
        | KorePattern::Nu { body, .. } => macro_or_alias_context(body, name)?,
        KorePattern::String(_)
        | KorePattern::Variable(_)
        | KorePattern::Top { .. }
        | KorePattern::Bottom { .. }
        | KorePattern::DomainValue { .. } => return None,
    };
    if let Some(label) = reference_pattern_context_label(pattern) {
        context.insert(0, format!("{label} (<unknown location>)"));
    }
    Some(context)
}

fn reference_pattern_context_label(pattern: &KorePattern) -> Option<&'static str> {
    match pattern {
        KorePattern::And { .. } => Some("\\and"),
        KorePattern::Or { .. } => Some("\\or"),
        KorePattern::Not { .. } => Some("\\not"),
        KorePattern::Next { .. } => Some("\\next"),
        KorePattern::Implies { .. } => Some("\\implies"),
        KorePattern::Iff { .. } => Some("\\iff"),
        KorePattern::Rewrites { .. } => Some("\\rewrites"),
        KorePattern::Exists { .. } => Some("\\exists"),
        KorePattern::Forall { .. } => Some("\\forall"),
        KorePattern::Mu { .. } => Some("\\mu"),
        KorePattern::Nu { .. } => Some("\\nu"),
        KorePattern::Ceil { .. } => Some("\\ceil"),
        KorePattern::Floor { .. } => Some("\\floor"),
        KorePattern::Equals { .. } => Some("\\equals"),
        KorePattern::In { .. } => Some("\\in"),
        _ => None,
    }
}

fn validate_singleton_implication_patterns(
    antecedent: &KorePattern,
    consequent: &KorePattern,
) -> Result<(), RpcFault> {
    let antecedent = super::strip_exists(antecedent);
    if matches!(antecedent, KorePattern::Or { arguments, .. } if arguments.len() != 1)
        || matches!(
            antecedent,
            KorePattern::Top { .. } | KorePattern::Mu { .. } | KorePattern::Nu { .. }
        )
    {
        return Err(RpcFault::implication(
            "The check implication step expects the antecedent term to be function-like.",
            vec![reference_pattern(antecedent)],
        ));
    }

    let consequent = super::strip_exists(consequent);
    if matches!(consequent, KorePattern::Or { arguments, .. } if arguments.len() != 1) {
        let sort = syntactic_pattern_sort(consequent)
            .map(ToString::to_string)
            .unwrap_or_else(|| "SortK{}".into());
        return Err(RpcFault::implication(
            "Term does not simplify to a singleton pattern",
            vec![format!(
                "RHS: \\and{{{sort}}}(     /* term: */ {}, \\and{{{sort}}}(     /* predicate: */ \\top{{{sort}}}(),     /* substitution: */ \\top{{{sort}}}() ))",
                reference_pattern(consequent)
            )],
        ));
    }
    Ok(())
}

fn special_implication_result(
    antecedent: &KorePattern,
    consequent: &KorePattern,
) -> Option<ImplicationResult> {
    let antecedent = super::strip_exists(antecedent);
    let consequent = super::strip_exists(consequent);
    let condition = |predicates| {
        Some(ImplicationCondition {
            predicates,
            substitution: Substitution::new(),
        })
    };
    if matches!(antecedent, KorePattern::Bottom { .. }) {
        Some(ImplicationResult {
            status: ImplicationStatus::Valid,
            condition: condition(vec![Predicate::False]),
            failure: None,
        })
    } else if matches!(consequent, KorePattern::Top { .. }) {
        Some(ImplicationResult {
            status: ImplicationStatus::Valid,
            condition: condition(Vec::new()),
            failure: None,
        })
    } else if matches!(consequent, KorePattern::Bottom { .. }) {
        Some(ImplicationResult {
            status: ImplicationStatus::Invalid,
            condition: condition(vec![Predicate::False]),
            failure: Some(ImplicationFailure::ConsequentCondition),
        })
    } else {
        None
    }
}

fn normalized_implication_syntax(original: &KorePattern, pattern: &Pattern) -> KorePattern {
    fn leaf_count(pattern: &KorePattern) -> usize {
        match pattern {
            KorePattern::And { arguments, .. } => arguments.iter().map(leaf_count).sum(),
            _ => 1,
        }
    }

    fn replace_constraint_leaves(
        pattern: &KorePattern,
        terms_remaining: &mut usize,
        constraints: &mut impl Iterator<Item = KorePattern>,
    ) -> KorePattern {
        match pattern {
            KorePattern::And { sort, arguments } => KorePattern::And {
                sort: sort.clone(),
                arguments: arguments
                    .iter()
                    .map(|argument| {
                        replace_constraint_leaves(argument, terms_remaining, constraints)
                    })
                    .collect(),
            },
            _ if *terms_remaining > 0 => {
                *terms_remaining -= 1;
                pattern.clone()
            }
            _ => constraints.next().unwrap_or_else(|| pattern.clone()),
        }
    }

    fn normalize_body(original: &KorePattern, pattern: &Pattern) -> KorePattern {
        let result_sort = pattern.term.sort();
        let mut constraints = pattern
            .constraints
            .iter()
            .map(|predicate| externalize::predicate_pattern(predicate, &result_sort))
            .collect::<Vec<_>>();
        constraints.sort();
        let leaves = leaf_count(original);
        if constraints.is_empty() || constraints.len() >= leaves {
            return original.clone();
        }
        let mut terms_remaining = leaves - constraints.len();
        let mut constraints = constraints.into_iter();
        let normalized =
            replace_constraint_leaves(original, &mut terms_remaining, &mut constraints);
        if terms_remaining == 0 && constraints.next().is_none() {
            normalized
        } else {
            original.clone()
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

fn validate_implication_variable_capture(
    antecedent: &KorePattern,
    consequent: &KorePattern,
) -> Result<(), RpcFault> {
    let mut antecedent_free = BTreeSet::new();
    super::collect_free_kore_variables(antecedent, &mut BTreeSet::new(), &mut antecedent_free);
    let (consequent_body, existentials) = leading_existentials(consequent);
    let captured = existentials
        .iter()
        .filter(|variable| antecedent_free.contains(*variable))
        .map(|variable| reference_variable_name(variable))
        .collect::<Vec<_>>();
    if captured.is_empty() {
        return Ok(());
    }
    Err(RpcFault::implication(
        format!(
            "Existentials capture free variables of the antecedent: {}",
            captured.join(", ")
        ),
        implication_pattern_context(antecedent, consequent_body, &existentials),
    ))
}

fn validate_implication_sorts(
    antecedent: &KorePattern,
    consequent: &KorePattern,
) -> Result<(), RpcFault> {
    let Some(antecedent_sort) = syntactic_pattern_sort(antecedent) else {
        return Ok(());
    };
    let Some(consequent_sort) = syntactic_pattern_sort(consequent) else {
        return Ok(());
    };
    if antecedent_sort == consequent_sort {
        return Ok(());
    }
    Err(RpcFault::implication(
        "Antecedent and consequent must have the same sort.",
        vec![
            format!("LHS sort: {}", reference_sort_name(antecedent_sort)),
            format!("RHS sort: {}", reference_sort_name(consequent_sort)),
        ],
    ))
}

fn implication_backend_fault(
    error: ImplicationError,
    antecedent: &KorePattern,
    consequent: &KorePattern,
    consequent_existentials: &BTreeSet<Variable>,
) -> RpcFault {
    match error {
        ImplicationError::ConsequentFreeVariables(variables) => {
            let (consequent_body, syntax_existentials) = leading_existentials(consequent);
            let names = variables
                .iter()
                .map(|variable| format!("Config{}", variable.name))
                .collect::<Vec<_>>();
            let existentials = if syntax_existentials.is_empty() {
                consequent_existentials
                    .iter()
                    .map(|variable| format!("Config{}", variable.name))
                    .collect::<Vec<_>>()
            } else {
                syntax_existentials
                    .iter()
                    .map(|variable| reference_variable_name(variable))
                    .collect()
            };
            RpcFault::implication(
                format!(
                    "The RHS must not have free variables not present in the LHS: {}",
                    names.join(", ")
                ),
                vec![
                    format!(
                        "LHS: {}",
                        reference_pattern(super::strip_exists(antecedent))
                    ),
                    format!("RHS: {}", reference_pattern(consequent_body)),
                    format!("existentials: [{}]", existentials.join(", ")),
                ],
            )
        }
        error => RpcFault::backend(format!("implication check failed: {error}")),
    }
}

fn leading_existentials(pattern: &KorePattern) -> (&KorePattern, Vec<&KoreVariable>) {
    let mut body = pattern;
    let mut variables = Vec::new();
    while let KorePattern::Exists {
        variable,
        body: next,
        ..
    } = body
    {
        variables.push(variable);
        body = next;
    }
    (body, variables)
}

fn implication_pattern_context(
    antecedent: &KorePattern,
    consequent: &KorePattern,
    existentials: &[&KoreVariable],
) -> Vec<String> {
    vec![
        format!(
            "LHS: {}",
            reference_pattern(super::strip_exists(antecedent))
        ),
        format!("RHS: {}", reference_pattern(consequent)),
        format!(
            "existentials: [{}]",
            existentials
                .iter()
                .map(|variable| reference_variable_name(variable))
                .collect::<Vec<_>>()
                .join(", ")
        ),
    ]
}

fn syntactic_pattern_sort(pattern: &KorePattern) -> Option<&KoreSort> {
    match pattern {
        KorePattern::Variable(variable) => Some(&variable.sort),
        KorePattern::Top { sort }
        | KorePattern::Bottom { sort }
        | KorePattern::And { sort, .. }
        | KorePattern::Or { sort, .. }
        | KorePattern::Not { sort, .. }
        | KorePattern::Next { sort, .. }
        | KorePattern::Implies { sort, .. }
        | KorePattern::Iff { sort, .. }
        | KorePattern::Rewrites { sort, .. }
        | KorePattern::Exists { sort, .. }
        | KorePattern::Forall { sort, .. }
        | KorePattern::DomainValue { sort, .. } => Some(sort),
        KorePattern::Ceil { result_sort, .. }
        | KorePattern::Floor { result_sort, .. }
        | KorePattern::Equals { result_sort, .. }
        | KorePattern::In { result_sort, .. } => Some(result_sort),
        KorePattern::Mu { variable, .. } | KorePattern::Nu { variable, .. } => Some(&variable.sort),
        KorePattern::String(_)
        | KorePattern::Application { .. }
        | KorePattern::AssociativeApplication { .. } => None,
    }
}

fn reference_sort_name(sort: &KoreSort) -> &str {
    match sort {
        KoreSort::Variable(name) | KoreSort::Application { name, .. } => name,
    }
}

fn reference_variable(variable: &KoreVariable) -> String {
    format!("{}:{}", reference_variable_name(variable), variable.sort)
}

fn reference_variable_name(variable: &KoreVariable) -> String {
    format!("Config{}", variable.name)
}

fn reference_pattern(pattern: &KorePattern) -> String {
    match pattern {
        KorePattern::Variable(variable) => reference_variable(variable),
        KorePattern::And { sort, arguments } => reference_connective("and", sort, arguments),
        KorePattern::Or { sort, arguments } => reference_connective("or", sort, arguments),
        KorePattern::Not { sort, argument } => {
            format!("\\not{{{sort}}}( {} )", reference_pattern(argument))
        }
        KorePattern::Mu { variable, body } => format!(
            "\\mu{{}}( {}, {} )",
            reference_variable(variable),
            reference_pattern(body)
        ),
        KorePattern::Nu { variable, body } => format!(
            "\\nu{{}}( {}, {} )",
            reference_variable(variable),
            reference_pattern(body)
        ),
        _ => pattern.to_string(),
    }
}

fn reference_connective(name: &str, sort: &KoreSort, arguments: &[KorePattern]) -> String {
    format!(
        "\\{name}{{{sort}}}( {} )",
        arguments
            .iter()
            .map(reference_pattern)
            .collect::<Vec<_>>()
            .join(", ")
    )
}

fn failed_rewrite_log(reason: &HaltReason) -> Option<Value> {
    let (reason, rule_id) = match reason {
        HaltReason::Stuck => ("No applicable rules found", None),
        HaltReason::Indeterminate(indeterminate) => match indeterminate {
            k_rust_backend::rewrite::IndeterminateReason::Match { rule_id, .. } => {
                ("Uncertain about unification of rule", Some(rule_id))
            }
            k_rust_backend::rewrite::IndeterminateReason::Requires { rule_id, .. }
            | k_rust_backend::rewrite::IndeterminateReason::Concreteness { rule_id, .. }
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
    serde_json::from_value(params.clone()).map_err(|_| RpcFault::invalid_params(params))
}

fn parse_json_value(source: &str) -> serde_json::Result<Value> {
    let mut deserializer = serde_json::Deserializer::from_str(source);
    deserializer.disable_recursion_limit();
    let value = Value::deserialize(&mut deserializer)?;
    deserializer.end()?;
    Ok(value)
}

fn encode_kore(pattern: &KorePattern) -> Result<Value, RpcFault> {
    let source = kore_json::to_string(pattern)
        .map_err(|error| RpcFault::backend(format!("could not encode KORE JSON: {error}")))?;
    serde_json::from_str(&source)
        .map_err(|error| RpcFault::backend(format!("could not encode KORE JSON: {error}")))
}

fn solver(definition: &BackendDefinition, options: Z3Options) -> Result<Z3Solver, RpcFault> {
    Z3Solver::with_options(definition, options)
        .map_err(|error| RpcFault::backend(format!("could not initialize Z3: {error:?}")))
}

fn execute_state(
    definition: &BackendDefinition,
    pattern: &Pattern,
    configuration_variables: &BTreeSet<Variable>,
) -> Result<Value, RpcFault> {
    let mut state = Map::new();
    let (predicates, substitution) =
        split_constraints(&pattern.constraints, configuration_variables);
    let term = substitute(&pattern.term, &substitution);
    state.insert("term".into(), encode_kore(&externalize::term(&term))?);
    let predicates = substitute_predicates(&predicates, &substitution);
    if let Some(predicate) =
        execution_constraints_pattern(definition, &predicates, &pattern.term.sort())
    {
        state.insert("predicate".into(), encode_kore(&predicate)?);
    }
    if let Some(substitution) = super::model_substitution(&substitution, &pattern.term.sort()) {
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
    if let Some(rule_predicate) =
        rule_constraints_pattern(&applied.rule_predicates, &applied.pattern.term.sort())
    {
        object.insert("rule-predicate".into(), encode_kore(&rule_predicate)?);
    }
    let (_, state_substitution) =
        split_constraints(&applied.pattern.constraints, configuration_variables);
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
    let substitution = substitution
        .iter()
        .map(|(variable, value)| {
            let name = if let Some(name) = variable.name.strip_prefix("Rule#") {
                format!("Rule{name}")
            } else if let Some(name) = variable.name.strip_prefix("Ex#") {
                format!("Ex{name}")
            } else {
                variable.name.to_string()
            };
            (
                variable.with_name(name),
                substitute(value, state_substitution),
            )
        })
        .collect();
    super::model_substitution(&substitution, result_sort).map(left_associate_conjunction)
}

fn left_associate_conjunction(pattern: KorePattern) -> KorePattern {
    let KorePattern::And { sort, arguments } = pattern else {
        return pattern;
    };
    let mut arguments = arguments.into_iter();
    let Some(first) = arguments.next() else {
        return KorePattern::And {
            sort,
            arguments: Vec::new(),
        };
    };
    let Some(second) = arguments.next() else {
        return first;
    };
    arguments.fold(
        KorePattern::And {
            sort: sort.clone(),
            arguments: vec![first, second],
        },
        |left, right| KorePattern::And {
            sort: sort.clone(),
            arguments: vec![left, right],
        },
    )
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
) -> (Vec<Predicate>, Substitution) {
    let (extracted, mut predicates) = extract_substitution(constraints);
    let mut substitution = Substitution::new();
    for (variable, value) in extracted {
        if configuration_variables.contains(&variable) {
            substitution.insert(variable, value);
        } else {
            predicates.push(Predicate::Equals(Term::variable(variable), value));
        }
    }
    (predicates, substitution)
}

fn constraints_pattern(
    constraints: &[Predicate],
    result_sort: &BackendSort,
) -> Option<KorePattern> {
    let mut predicates = constraints
        .iter()
        .filter(|predicate| !matches!(predicate, Predicate::True))
        .map(|predicate| externalize::predicate_pattern(predicate, result_sort));
    let first = predicates.next()?;
    Some(predicates.fold(first, |left, right| KorePattern::And {
        sort: externalize::sort(result_sort),
        arguments: vec![left, right],
    }))
}

fn execution_constraints_pattern(
    definition: &BackendDefinition,
    constraints: &[Predicate],
    result_sort: &BackendSort,
) -> Option<KorePattern> {
    let mut predicates = constraints
        .iter()
        .filter(|predicate| !matches!(predicate, Predicate::True))
        .map(|predicate| {
            externalize::booster_predicate_pattern(definition, predicate, result_sort)
        });
    let first = predicates.next()?;
    Some(predicates.fold(first, |left, right| KorePattern::And {
        sort: externalize::sort(result_sort),
        arguments: vec![left, right],
    }))
}

fn rule_constraints_pattern(
    constraints: &[Predicate],
    result_sort: &BackendSort,
) -> Option<KorePattern> {
    let mut predicates = constraints
        .iter()
        .filter(|predicate| !matches!(predicate, Predicate::True))
        .map(|predicate| externalize::booster_rule_predicate_pattern(predicate, result_sort));
    let first = predicates.next()?;
    Some(predicates.fold(first, |left, right| KorePattern::And {
        sort: externalize::sort(result_sort),
        arguments: vec![left, right],
    }))
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
        ImplicationStatus::Indeterminate => "unknown",
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
        let antecedent_variable = match super::strip_exists(antecedent) {
            KorePattern::Variable(variable) => Some(variable.name.as_str()),
            _ => None,
        };
        let substitution = super::implication_substitution(
            &condition.substitution,
            result_sort,
            antecedent_variable,
        )
        .unwrap_or_else(|| KorePattern::Top {
            sort: externalize::sort(result_sort),
        });
        let predicate =
            constraints_pattern(&condition.predicates, result_sort).unwrap_or_else(|| {
                KorePattern::Top {
                    sort: externalize::sort(result_sort),
                }
            });
        output["condition"] = json!({
            "substitution": encode_kore(&substitution)?,
            "predicate": encode_kore(&predicate)?,
        });
    }
    Ok(output)
}

pub(super) fn serve(
    session: BackendSession,
    address: impl ToSocketAddrs,
    smt_options: Z3Options,
) -> Result<(), Box<dyn Error>> {
    let listener = TcpListener::bind(address)?;
    eprintln!("KORE JSON-RPC listening on {}", listener.local_addr()?);
    let service = Arc::new(Mutex::new(RpcService::with_smt_options(
        session,
        smt_options,
    )));
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

fn serve_connection(
    stream: TcpStream,
    service: Arc<Mutex<RpcService>>,
) -> Result<(), Box<dyn Error>> {
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
                let response = control.token.scope(|| {
                    service
                        .lock()
                        .map_err(|_| io::Error::other("KORE JSON-RPC session lock was poisoned"))
                        .map(|mut service| service.handle_line(&line))
                })?;
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
    let mut read_error = None;
    loop {
        let message = match read_json_message(&mut reader, &mut buffer) {
            Ok(Some(message)) => message,
            Ok(None) => break,
            Err(error) => {
                read_error = Some(error);
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
            {
                write_response(&writer, response)?;
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
    drop(sender);
    worker
        .join()
        .map_err(|_| io::Error::other("KORE JSON-RPC worker panicked"))??;
    if let Some(error) = read_error {
        return Err(error.into());
    }
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
          symbol state{}() : SortState{} [constructor{}()]
          symbol next{}() : SortState{} [constructor{}()]
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
                  symbol macroValue{}() : SortK{} [functional{}(), macro{}()]
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

    fn symbolic_branch_service() -> RpcService {
        RpcService::new(BackendSession::new(
            parse_definition(
                r#"[]
                module TEST
                  hooked-sort SortInt{} [hook{}("INT.Int"), hasDomainValues{}()]
                  hooked-sort SortBool{} [hook{}("BOOL.Bool"), hasDomainValues{}()]
                  symbol wrap{}(SortInt{}) : SortInt{} [constructor{}()]
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
    }

    #[test]
    fn implication_rejects_a_non_function_like_antecedent_with_reference_context() {
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
                    "context": [r#"\or{SortK{}}( ConfigX:SortK{}, \not{SortK{}}( ConfigX:SortK{} ) )"#],
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
    fn implication_keeps_nested_consequent_existentials_on_the_left() {
        let sort = BackendSort::simple("SortK");
        let variable = Variable::new("X!exists0", sort.clone());
        let value = Term::domain_value(sort.clone(), "value");
        let substitution = Substitution::from([(variable, value)]);

        let output = crate::implication_substitution(&substitution, &sort, None)
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
        let KorePattern::And { arguments, .. } = normalized else {
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
    fn implication_rejects_a_non_singleton_consequent_with_reference_context() {
        let error = implication_error(
            "X:SortK{}",
            r#"\or{SortK{}}(X:SortK{}, \not{SortK{}}(X:SortK{}))"#,
        );
        assert_eq!(error["code"], 4);
        assert_eq!(
            error["data"]["error"],
            "Term does not simplify to a singleton pattern"
        );
        assert_eq!(
            error["data"]["context"][0],
            r#"RHS: \and{SortK{}}(     /* term: */ \or{SortK{}}( ConfigX:SortK{}, \not{SortK{}}( ConfigX:SortK{} ) ), \and{SortK{}}(     /* predicate: */ \top{SortK{}}(),     /* substitution: */ \top{SortK{}}() ))"#
        );
    }

    #[test]
    fn implication_rejects_existential_name_capture_with_reference_context() {
        let error = implication_error("X:SortK{}", r#"\exists{SortK{}}(X:SortK{}, X:SortK{})"#);
        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": [
                        "LHS: ConfigX:SortK{}",
                        "RHS: ConfigX:SortK{}",
                        "existentials: [ConfigX]",
                    ],
                    "error": "Existentials capture free variables of the antecedent: ConfigX",
                },
            })
        );
    }

    #[test]
    fn implication_rejects_free_consequent_variables_with_reference_context() {
        let error = implication_error(
            "X:SortK{}",
            r#"\exists{SortK{}}(Z:SortK{}, \and{SortK{}}(Y:SortK{}, Z:SortK{}))"#,
        );
        assert_eq!(
            error,
            json!({
                "code": 4,
                "message": "Implication check error",
                "data": {
                    "context": [
                        "LHS: ConfigX:SortK{}",
                        r#"RHS: \and{SortK{}}( ConfigY:SortK{}, ConfigZ:SortK{} )"#,
                        "existentials: [ConfigZ]",
                    ],
                    "error": "The RHS must not have free variables not present in the LHS: ConfigY",
                },
            })
        );
    }

    #[test]
    fn implication_rejects_fixpoint_antecedents_as_non_function_like() {
        let error = implication_error(
            r#"\mu{}(@A:SortK{}, @A:SortK{})"#,
            r#"\exists{SortK{}}(Z:SortK{}, Z:SortK{})"#,
        );
        assert_eq!(error["code"], 4);
        assert_eq!(
            error["data"]["context"],
            json!([r#"\mu{}( Config@A:SortK{}, Config@A:SortK{} )"#])
        );
        assert_eq!(
            error["data"]["error"],
            "The check implication step expects the antecedent term to be function-like."
        );
    }

    #[test]
    fn implication_macro_errors_include_the_reference_validation_path() {
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
                    "context": [
                        r#"\and (<unknown location>)"#,
                        r#"\and (<unknown location>)"#,
                        r#"\equals (<unknown location>)"#,
                        "symbol or alias 'macroValue' (<unknown location>)",
                    ],
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
                    "context": ["LHS sort: S1", "RHS sort: SortK"],
                    "error": "Antecedent and consequent must have the same sort.",
                },
            })
        );
    }

    #[test]
    fn protocol_parser_accepts_deep_json_without_serde_recursion_limits() {
        let depth = 300;
        let source = format!("{}null{}", "[".repeat(depth), "]".repeat(depth));
        assert!(parse_json_value(&source).is_ok());
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
    fn cancel_requests_inside_batches_report_the_reference_error() {
        let mut service = service();
        let response: Value = serde_json::from_str(
            &service
                .handle_line(r#"[{"jsonrpc":"2.0","id":7,"method":"cancel"}]"#)
                .unwrap(),
        )
        .unwrap();

        assert_eq!(
            response,
            json!([{
                "jsonrpc": "2.0",
                "id": 7,
                "error": {
                    "code": -32001,
                    "message": "Cancel request unsupported in batch mode",
                    "data": null,
                },
            }])
        );
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

        let definition = service.definition(Some("EXTRA")).unwrap();
        assert_eq!(definition.main_module.as_ref(), id);
    }

    #[test]
    fn add_module_reports_reference_validation_errors() {
        let mut service = service();
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
    }

    #[test]
    fn missing_requested_modules_use_the_reference_error_shape() {
        let mut service = service();
        let state = encode_kore(&parse_pattern("state{}()").unwrap()).unwrap();
        let response = request(
            &mut service,
            1,
            "execute",
            json!({ "state": state, "module": "MISSING" }),
        );

        assert_eq!(
            response["error"],
            json!({
                "code": 3,
                "message": "Could not find module",
                "data": "MISSING",
            })
        );
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
    fn execute_can_assume_the_current_configuration_is_defined() {
        let definition = parse_definition(
            r#"[]
            module MAIN
                sort SortS{} [hasDomainValues{}()]
                symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
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
    fn retains_a_cycle_breaking_equation_outside_the_rpc_substitution() {
        let sort = BackendSort::simple("SortState");
        let x = Variable::new("X", sort.clone());
        let y = Variable::new("Y", sort);
        let constraints = vec![
            Predicate::Equals(Term::variable(y.clone()), Term::variable(x.clone())),
            Predicate::Equals(Term::variable(x.clone()), Term::variable(y.clone())),
        ];

        let (predicates, substitution) =
            split_constraints(&constraints, &BTreeSet::from([x.clone(), y.clone()]));

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
            pattern,
            KorePattern::And { arguments, .. }
                if arguments.len() == 2
                    && matches!(&arguments[0], KorePattern::And { arguments, .. }
                        if arguments.len() == 2)
                    && matches!(&arguments[1], KorePattern::Equals { .. })
        ));
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

    #[test]
    fn serves_multiple_newline_delimited_requests_on_one_socket() {
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
            json!({ "jsonrpc": "2.0", "method": "cancel" }),
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
        client.shutdown(Shutdown::Write).unwrap();
        let mut responses = String::new();
        client.read_to_string(&mut responses).unwrap();
        worker.join().unwrap();

        let responses = responses
            .lines()
            .map(|line| serde_json::from_str::<Value>(line).unwrap())
            .collect::<Vec<_>>();
        assert_eq!(
            responses.len(),
            2,
            "notifications must not receive a response"
        );
        assert_eq!(responses[0]["error"]["code"], -32601);
        assert_eq!(responses[1]["result"]["satisfiable"], "Sat");
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
                symbol wrap{}(SortS{}) : SortS{} [constructor{}()]
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

    fn request(service: &mut RpcService, id: u64, method: &str, params: Value) -> Value {
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
