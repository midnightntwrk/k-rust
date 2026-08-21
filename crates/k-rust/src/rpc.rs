//! Stateful KORE JSON-RPC 2.0 dispatch and raw TCP transport.

use std::{
    collections::{BTreeSet, VecDeque},
    error::Error,
    io::{self, BufRead, BufReader, BufWriter, Write},
    net::{TcpListener, TcpStream, ToSocketAddrs},
    sync::{
        Arc, Mutex,
        atomic::{AtomicU8, Ordering},
        mpsc,
    },
    thread,
    time::Duration,
};

use k_rust::kore::{ast::Pattern as KorePattern, json as kore_json, parser::parse_module};
use k_rust_backend::{
    cancellation::{CancellationToken, cancellation_requested},
    definition::BackendDefinition,
    externalize,
    implication::{ImplicationResult, ImplicationStatus, check_implication_with_existentials},
    rewrite::{
        AppliedRule, ExecutionBranchMode, ExecutionMode, ExecutionOptions, HaltReason, Pattern,
        TraceKind, execute_with_solver, substitute_predicates,
    },
    rule::Predicate,
    session::BackendSession,
    simplify::{SimplificationOptions, simplify_and_decide_predicate_with_solver},
    smt::{ModelResult, SmtSolver, Z3Solver},
    substitution::{Substitution, substitute},
    term::{Sort as BackendSort, TermKind, Variable},
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

    fn module(module: &str, error: impl ToString) -> Self {
        Self {
            code: 3,
            message: "Could not find module".into(),
            data: Some(json!({ "module": module, "error": error.to_string() })),
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
    pub(super) fn new(session: BackendSession) -> Self {
        Self { session }
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
            result
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
            log_failed_rewrites: _log_failed_rewrites,
            booster_only,
            haskell_logging,
        } = params;
        let _booster_only = booster_only;
        reject_haskell_logging(&haskell_logging)?;
        if assume_state_defined {
            return Err(RpcFault::backend(
                "assume-state-defined is not yet supported by the Rust backend",
            ));
        }
        let definition = self.definition(module.as_deref())?;
        let syntax = state.0;
        let initial = definition
            .internalize_pattern(&syntax, &[])
            .map_err(RpcFault::pattern)?;
        let configuration_variables = pattern_variables(&initial);
        let solver = solver(&definition)?;
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
            HaltReason::Branch { branches } => (
                "branching",
                Some(
                    branches
                        .iter()
                        .rev()
                        .map(|applied| execute_applied_state(applied, &configuration_variables))
                        .collect::<Result<Vec<_>, _>>()?,
                ),
                None,
            ),
            HaltReason::CutPointRule { rule, next_states } => (
                "cut-point-rule",
                Some(
                    next_states
                        .iter()
                        .map(|applied| execute_state(&applied.pattern, &configuration_variables))
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
            execute_state(&leaf.pattern, &configuration_variables)?,
        );
        if let Some(next_states) = next_states {
            output.insert("next-states".into(), Value::Array(next_states));
        }
        if log_successful_rewrites {
            let logs = leaf
                .trace
                .iter()
                .filter(|entry| entry.kind == TraceKind::Rewrite)
                .map(|entry| {
                    json!({
                        "tag": "rewrite",
                        "origin": "kore-rpc",
                        "result": {
                            "tag": "success",
                            "rule-id": entry.unique_id,
                        },
                    })
                })
                .collect();
            output.insert("logs".into(), Value::Array(logs));
        }
        Ok(Value::Object(output))
    }

    fn simplify(&mut self, params: SimplifyParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        reject_haskell_logging(&params.haskell_logging)?;
        let definition = self.definition(params.module.as_deref())?;
        let syntax = params.state.0;
        let (predicate, result_sort) = definition
            .internalize_predicate(&syntax, &[])
            .map_err(RpcFault::pattern)?;
        let solver = solver(&definition)?;
        let simplified = simplify_and_decide_predicate_with_solver(
            &definition,
            &predicate,
            &[],
            SimplificationOptions::default(),
            &solver,
        )
        .map_err(|error| RpcFault::backend(format!("could not simplify pattern: {error:?}")))?;
        Ok(json!({ "state": encode_kore(&externalize::ml_pattern(&simplified, &result_sort))? }))
    }

    fn add_module(&mut self, params: AddModuleParams) -> Result<Value, RpcFault> {
        reject_haskell_logging(&params.haskell_logging)?;
        let module = parse_module(&params.module)
            .map_err(|error| RpcFault::backend(format!("could not parse module: {error}")))?;
        let id = self
            .session
            .add_module(&params.module, module, params.name_as_id)
            .map_err(|error| RpcFault::backend(format!("could not add module: {error}")))?;
        Ok(json!({ "module": id }))
    }

    fn get_model(&mut self, params: GetModelParams) -> Result<Value, RpcFault> {
        let _booster_only = params.booster_only;
        reject_haskell_logging(&params.haskell_logging)?;
        let definition = self.definition(params.module.as_deref())?;
        let syntax = params.state.0;
        let Some((predicate, result_sort)) = definition
            .internalize_model_predicate(&syntax, &[])
            .map_err(RpcFault::pattern)?
        else {
            return Ok(json!({ "satisfiable": "Unknown" }));
        };
        let solver = solver(&definition)?;
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
        reject_haskell_logging(&params.haskell_logging)?;
        if params.assume_defined {
            return Err(RpcFault::backend(
                "assume-defined is not yet supported by the Rust backend",
            ));
        }
        let definition = self.definition(params.module.as_deref())?;
        let antecedent = params.antecedent.0;
        let consequent = params.consequent.0;
        definition
            .validate_implication_pattern(&antecedent)
            .map_err(RpcFault::pattern)?;
        definition
            .validate_implication_pattern(&consequent)
            .map_err(RpcFault::pattern)?;
        super::reject_non_singleton_implication_pattern(&antecedent, "antecedent")
            .map_err(|error| RpcFault::pattern(error.to_string()))?;
        super::reject_non_singleton_implication_pattern(&consequent, "consequent")
            .map_err(|error| RpcFault::pattern(error.to_string()))?;
        super::reject_implication_variable_capture(&antecedent, &consequent)
            .map_err(|error| RpcFault::pattern(error.to_string()))?;
        let sort_variables = super::implication_sort_variables(&antecedent, &consequent);
        let (antecedent_pattern, antecedent_existentials) = definition
            .internalize_implication_pattern(&antecedent, &sort_variables)
            .map_err(RpcFault::pattern)?;
        let result_sort = antecedent_pattern.term.sort();
        let result = if matches!(super::strip_exists(&consequent), KorePattern::Not { .. }) {
            ImplicationResult {
                status: ImplicationStatus::Invalid,
                condition: None,
                failure: None,
            }
        } else {
            let (consequent_pattern, consequent_existentials) = definition
                .internalize_implication_pattern(&consequent, &sort_variables)
                .map_err(RpcFault::pattern)?;
            if result_sort != consequent_pattern.term.sort() {
                return Err(RpcFault::pattern("antecedent and consequent sorts differ"));
            }
            let solver = solver(&definition)?;
            check_implication_with_existentials(
                &definition,
                &antecedent_pattern,
                &antecedent_existentials,
                &consequent_pattern,
                &consequent_existentials,
                &solver,
            )
            .map_err(|error| RpcFault::backend(format!("implication check failed: {error}")))?
        };
        implication_result(&antecedent, &consequent, &result_sort, result)
    }
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

fn reject_haskell_logging(entries: &[String]) -> Result<(), RpcFault> {
    if entries.is_empty() {
        Ok(())
    } else {
        Err(RpcFault::backend(
            "Haskell log entry selection is not supported by the Rust backend",
        ))
    }
}

fn encode_kore(pattern: &KorePattern) -> Result<Value, RpcFault> {
    let source = kore_json::to_string(pattern)
        .map_err(|error| RpcFault::backend(format!("could not encode KORE JSON: {error}")))?;
    serde_json::from_str(&source)
        .map_err(|error| RpcFault::backend(format!("could not encode KORE JSON: {error}")))
}

fn solver(definition: &BackendDefinition) -> Result<Z3Solver, RpcFault> {
    Z3Solver::new(definition)
        .map_err(|error| RpcFault::backend(format!("could not initialize Z3: {error:?}")))
}

fn execute_state(
    pattern: &Pattern,
    configuration_variables: &BTreeSet<Variable>,
) -> Result<Value, RpcFault> {
    let mut state = Map::new();
    let (predicates, substitution) =
        split_constraints(&pattern.constraints, configuration_variables);
    let term = substitute(&pattern.term, &substitution);
    state.insert("term".into(), encode_kore(&externalize::term(&term))?);
    let predicates = substitute_predicates(&predicates, &substitution);
    if let Some(predicate) = constraints_pattern(&predicates, &pattern.term.sort()) {
        state.insert("predicate".into(), encode_kore(&predicate)?);
    }
    if let Some(substitution) = super::model_substitution(&substitution, &pattern.term.sort()) {
        state.insert("substitution".into(), encode_kore(&substitution)?);
    }
    Ok(Value::Object(state))
}

fn execute_applied_state(
    applied: &AppliedRule,
    configuration_variables: &BTreeSet<Variable>,
) -> Result<Value, RpcFault> {
    let mut state = execute_state(&applied.pattern, configuration_variables)?;
    let object = state
        .as_object_mut()
        .expect("execute_state always returns an object");
    object.insert("rule-id".into(), Value::String(applied.unique_id.clone()));
    if let Some(rule_predicate) =
        constraints_pattern(&applied.rule_predicates, &applied.pattern.term.sort())
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
    super::model_substitution(&substitution, result_sort)
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
    let mut predicates = Vec::new();
    let mut substitution = Substitution::new();
    for constraint in constraints {
        let binding = match constraint {
            Predicate::Equals(left, right) => {
                variable_binding(left, right, configuration_variables)
                    .or_else(|| variable_binding(right, left, configuration_variables))
            }
            _ => None,
        };
        if let Some((variable, value)) = binding
            && !substitution.contains_key(&variable)
        {
            substitution.insert(variable, value);
        } else {
            predicates.push(constraint.clone());
        }
    }
    (predicates, substitution)
}

fn variable_binding(
    variable: &k_rust_backend::term::Term,
    value: &k_rust_backend::term::Term,
    configuration_variables: &BTreeSet<Variable>,
) -> Option<(Variable, k_rust_backend::term::Term)> {
    let TermKind::Variable(variable) = variable.kind() else {
        return None;
    };
    (configuration_variables.contains(variable) && !value.attributes().variables.contains(variable))
        .then(|| (variable.clone(), value.clone()))
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
        let substitution = super::implication_substitution(&condition.substitution, result_sort)
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
) -> Result<(), Box<dyn Error>> {
    let listener = TcpListener::bind(address)?;
    eprintln!("KORE JSON-RPC listening on {}", listener.local_addr()?);
    let service = Arc::new(Mutex::new(RpcService::new(session)));
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
    let reader = BufReader::new(stream.try_clone()?);
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

    let mut read_error = None;
    for line in reader.lines() {
        let line = match line {
            Ok(line) => line,
            Err(error) => {
                read_error = Some(error);
                break;
            }
        };
        if is_standalone_cancel(&line) {
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
        let control = Arc::new(RequestControl::new(&line));
        controls
            .lock()
            .map_err(|_| io::Error::other("KORE JSON-RPC request queue was poisoned"))?
            .push_back(Arc::clone(&control));
        if sender.send((line, control)).is_err() {
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
        io::{Read, Write},
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
                "origin": "kore-rpc",
                "result": { "tag": "success", "rule-id": "rule-id" },
            }])
        );
    }

    #[test]
    fn projects_solved_configuration_equalities_as_substitutions() {
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

        let state = execute_state(&pattern, &BTreeSet::from([variable])).unwrap();
        assert_eq!(state["term"]["term"]["tag"], "DV");
        assert_eq!(state["term"]["term"]["value"], "resolved");
        assert_eq!(state["substitution"]["term"]["tag"], "Equals");
        assert_eq!(state["substitution"]["term"]["first"]["name"], "X");
        assert_eq!(state["substitution"]["term"]["second"]["value"], "resolved");
        assert!(state.get("predicate").is_none());
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

        let simplify = request(&mut service, 1, "simplify", json!({ "state": state }));
        assert_eq!(simplify["result"]["state"]["term"]["tag"], "App");

        let implies = request(
            &mut service,
            2,
            "implies",
            json!({ "antecedent": state, "consequent": state }),
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
