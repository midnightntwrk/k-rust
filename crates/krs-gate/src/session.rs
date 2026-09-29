//! Newline-delimited JSON native backend session.

use crate::{
    compile::compile_ir,
    configuration::Configuration,
    kore_digest,
    pattern::{self, PatternContext},
};
use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ProveRequest},
    kore::{
        ast::Pattern,
        json as kore_json,
        parser::{parse_definition, parse_pattern},
    },
};
use krs_ir::measure::Timings;
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
    collections::BTreeMap,
    error::Error,
    io::{self, BufRead, Write},
    path::Path,
};

fn required_string<'a>(request: &'a Value, key: &str) -> Result<&'a str, Box<dyn Error>> {
    request
        .get(key)
        .and_then(Value::as_str)
        .ok_or_else(|| format!("request field `{key}` must be a string").into())
}

fn pattern_json(source: &str) -> Result<Value, Box<dyn Error>> {
    let pattern = parse_pattern(source)?;
    let source = kore_json::to_string(&pattern)?;
    let mut deserializer = serde_json::Deserializer::from_str(&source);
    deserializer.disable_recursion_limit();
    Ok(Value::deserialize(&mut deserializer)?)
}

fn execute(
    backend: &mut Backend,
    request: &Value,
) -> Result<(Value, Option<Pattern>), Box<dyn Error>> {
    let max_depth = match request.get("max_depth") {
        None | Some(Value::Null) => None,
        Some(value) => Some(
            value
                .as_u64()
                .ok_or("request field `max_depth` must be an unsigned integer or null")?,
        ),
    };
    let max_simplification_iterations =
        match request.get("max_simplification_iterations") {
            None => ExecuteRequest::default().max_simplification_iterations,
            Some(value) => usize::try_from(value.as_u64().ok_or(
                "request field `max_simplification_iterations` must be an unsigned integer",
            )?)?,
        };
    let mut result = backend.execute(ExecuteRequest {
        state: pattern_json(required_string(request, "pattern")?)?,
        max_depth,
        max_simplification_iterations,
        ..ExecuteRequest::default()
    })?;
    if !request
        .get("trace")
        .and_then(Value::as_bool)
        .unwrap_or(false)
    {
        for leaf in &mut result.leaves {
            leaf.trace.clear();
        }
    }
    let retained = if request.get("keep").is_some() {
        if result.leaves.len() != 1 {
            return Err(format!(
                "execute with `keep` requires exactly one leaf, got {}",
                result.leaves.len()
            )
            .into());
        }
        let source = serde_json::to_string(&result.leaves[0].state)?;
        Some(kore_json::from_str(&source)?)
    } else {
        None
    };
    let output = if retained.is_some() {
        let leaves = result
            .leaves
            .iter()
            .map(|leaf| {
                json!({
                    "reason": leaf.reason, "depth": leaf.depth, "detail": leaf.detail,
                    "trace": leaf.trace,
                })
            })
            .collect::<Vec<_>>();
        json!({"modality": result.modality, "leaves": leaves})
    } else {
        serde_json::to_value(result)?
    };
    Ok((output, retained))
}

fn prove(backend: &mut Backend, request: &Value) -> Result<Value, Box<dyn Error>> {
    let result = backend.prove(ProveRequest {
        claim: Some(required_string(request, "claim")?.to_owned()),
        ..ProveRequest::default()
    })?;
    Ok(serde_json::to_value(result)?)
}

/// A session with at most one loaded definition.
#[derive(Default)]
pub struct Session {
    backend: Option<Backend>,
    configuration: Option<Configuration>,
    patterns: Option<PatternContext>,
    states: BTreeMap<String, Pattern>,
    load_attempted: bool,
}

impl Session {
    /// Create an unloaded session.
    #[must_use]
    pub fn new() -> Self {
        Self::default()
    }

    /// Process one request, returning a response or a fatal protocol error.
    ///
    /// Operation failures are returned as response errors and preserve the session.
    ///
    /// # Errors
    ///
    /// Returns an error for a protocol violation.
    pub fn dispatch(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let id = required_string(request, "id")?.to_owned();
        let operation = required_string(request, "operation")?;
        if !matches!(
            operation,
            "definition.load"
                | "configure"
                | "execute"
                | "prove"
                | "kore.read"
                | "kore.digest"
                | "observe"
                | "expect"
        ) {
            return Err(format!("unsupported operation `{operation}`").into());
        }
        if self.backend.is_none() && !matches!(operation, "definition.load" | "kore.digest") {
            return Err(format!("operation `{operation}` before definition.load").into());
        }
        if self.load_attempted && operation == "definition.load" {
            return Err("definition.load may occur only once".into());
        }
        if operation == "definition.load" {
            self.load_attempted = true;
        }
        let result: Result<Value, Box<dyn Error>> = match operation {
            "definition.load" => self.load(request),
            "configure" => self.configure(request),
            "execute" => self.execute(request),
            "prove" => prove(self.backend.as_mut().ok_or("backend not loaded")?, request),
            "kore.read" => self.read(request),
            "kore.digest" => Self::digest(request),
            "observe" => self.observe(request),
            "expect" => self.expect(request),
            _ => unreachable!("validated operation"),
        };
        Ok(match result {
            Ok(value) => json!({"id": id, "result": value}),
            Err(error) => json!({"id": id, "error": {"message": error.to_string()}}),
        })
    }

    fn load(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let module = required_string(request, "module")?;
        if request.get("kore").is_some() {
            return Err("definition.load does not accept `kore`".into());
        }
        let path = required_string(request, "definition_ir")?;
        let (artifacts, context) = compile_ir(&mut Timings::disabled(), Path::new(path))?;
        if context.frontend_definition.main_module != module {
            return Err(format!(
                "Definition IR main module is `{}`, not requested `{module}`",
                context.frontend_definition.main_module
            )
            .into());
        }
        let patterns =
            PatternContext::from_definition(&parse_definition(&artifacts.definition_kore)?)
                .with_frontend_cells(&context.frontend_definition)?;
        let configuration = Configuration::new(context)?;
        let backend = Backend::new(
            &artifacts.definition_kore,
            module.to_owned(),
            BackendOptions::default(),
        )?;
        self.backend = Some(backend);
        self.configuration = Some(configuration);
        self.patterns = Some(patterns);
        Ok(json!({"module": module}))
    }

    fn configure(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let variables = request
            .get("variables")
            .and_then(Value::as_object)
            .ok_or("request field `variables` must be an object")?;
        self.configuration
            .as_mut()
            .ok_or("configuration not loaded")?
            .configure(variables)
    }

    fn execute(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let keep = request
            .get("keep")
            .map(|_| required_string(request, "keep"))
            .transpose()?;
        let (result, state) = execute(self.backend.as_mut().ok_or("backend not loaded")?, request)?;
        if let (Some(name), Some(state)) = (keep, state) {
            self.states.insert(name.to_owned(), state);
        }
        Ok(result)
    }

    fn read(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let name = required_string(request, "keep")?;
        let state = parse_pattern(required_string(request, "text")?)?;
        self.states.insert(name.to_owned(), state);
        Ok(json!({"state": name}))
    }

    fn digest(request: &Value) -> Result<Value, Box<dyn Error>> {
        let kore = Path::new(required_string(request, "kore")?);
        let semantics = Path::new(required_string(request, "semantics")?);
        Ok(json!({"sha256": kore_digest::digest_file(kore, semantics)?}))
    }

    fn state(&self, request: &Value) -> Result<&Pattern, Box<dyn Error>> {
        let name = required_string(request, "state")?;
        self.states
            .get(name)
            .ok_or_else(|| format!("unknown retained state `{name}`").into())
    }

    fn observe(&self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let names = request
            .get("cells")
            .and_then(Value::as_array)
            .ok_or("request field `cells` must be an array")?;
        let context = self
            .patterns
            .as_ref()
            .ok_or("definition metadata not loaded")?;
        let state = self.state(request)?;
        let mut cells = serde_json::Map::new();
        for name in names {
            let name = name.as_str().ok_or("cell names must be strings")?;
            let cell_value = context.normalize(pattern::cell(state, name)?.clone());
            cells.insert(
                name.to_owned(),
                json!({"kore": cell_value.to_string(), "size": context.cell_collection_size(name, &cell_value)}),
            );
        }
        Ok(Value::Object(cells))
    }

    fn expect(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let cell_name = required_string(request, "cell")?;
        let fields = ["text", "size", "head"]
            .into_iter()
            .filter(|field| request.get(*field).is_some())
            .collect::<Vec<_>>();
        if fields.len() != 1 {
            return Err("expect requires exactly one of `text`, `size`, or `head`".into());
        }
        let context = self
            .patterns
            .as_ref()
            .ok_or("definition metadata not loaded")?;
        let actual = context.normalize(pattern::cell(self.state(request)?, cell_name)?.clone());
        if let Some(size) = request.get("size") {
            let expected = size
                .as_u64()
                .ok_or("expect size must be an unsigned integer")?;
            let count = context
                .cell_collection_size(cell_name, &actual)
                .ok_or_else(|| {
                    format!(
                        "<{cell_name}> is not a collection (declared sort {:?})",
                        context.cell_sort(cell_name)
                    )
                })?;
            return Ok(
                json!({"met": u64::try_from(count)? == expected, "expected": expected.to_string(), "actual": count.to_string()}),
            );
        }
        let head = fields[0] == "head";
        let source = required_string(request, fields[0])?;
        let sort = context
            .cell_sort(cell_name)
            .ok_or_else(|| format!("unknown cell <{cell_name}>"))?
            .clone();
        let configuration = self
            .configuration
            .as_mut()
            .ok_or("configuration not loaded")?;
        let expected = if head {
            configuration.parse_head(cell_name, source)?
        } else {
            configuration.parse_cell(cell_name, &sort, source)?
        };
        let expected = self
            .patterns
            .as_ref()
            .ok_or("definition metadata not loaded")?
            .normalize(expected);
        let actual = if head {
            if let Pattern::Application { symbol, arguments } = &actual
                && symbol.name == "kseq"
                && let [first, _] = arguments.as_slice()
            {
                first.clone()
            } else {
                return Err(format!("<{cell_name}> does not contain a K sequence head").into());
            }
        } else {
            actual
        };
        Ok(
            json!({"met": expected == actual, "expected": expected.to_string(), "actual": actual.to_string()}),
        )
    }
}

/// Serve a session using the given input and output streams.
///
/// A protocol violation terminates the stream with an error.
///
/// # Errors
///
/// Returns an error for invalid input, a protocol violation, or failed output.
pub fn serve<R: BufRead, W: Write>(input: R, mut output: W) -> Result<(), Box<dyn Error>> {
    let mut session = Session::new();
    for line in input.lines() {
        let request: Value = serde_json::from_str(&line?)?;
        let response = session.dispatch(&request)?;
        serde_json::to_writer(&mut output, &response)?;
        output.write_all(b"\n")?;
        output.flush()?;
    }
    Ok(())
}

/// Run a session on standard input and standard output in a 64 MiB stack worker.
///
/// # Errors
///
/// Returns an error when the worker or session fails.
pub fn run() -> Result<(), Box<dyn Error>> {
    let result = std::thread::Builder::new()
        .name("krs-native-backend".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| {
            let stdin = io::stdin();
            let stdout = io::stdout();
            serve(stdin.lock(), io::BufWriter::new(stdout.lock()))
                .map_err(|error| error.to_string())
        })?
        .join()
        .map_err(|_| "native backend thread panicked")?;
    result.map_err(Into::into)
}

#[cfg(test)]
mod tests {
    use super::Session;
    use serde_json::json;

    #[test]
    fn rejects_protocol_violations_before_loading() {
        let mut session = Session::new();
        let digest = session
            .dispatch(&json!({
                "id": "digest", "operation": "kore.digest",
                "kore": "/nonexistent/krs-gate-definition.kore",
                "semantics": "/tmp/semantics.k"
            }))
            .unwrap();
        assert_eq!(digest["id"], "digest");
        assert!(digest["error"]["message"].is_string());
        assert!(
            session
                .dispatch(&json!({"operation": "definition.load"}))
                .is_err()
        );
        assert!(session.dispatch(&json!({"id": "1"})).is_err());
        assert!(
            session
                .dispatch(&json!({"id": "1", "operation": "execute"}))
                .is_err()
        );
        assert!(
            session
                .dispatch(&json!({"id": "1", "operation": "configure"}))
                .is_err()
        );
        for operation in ["kore.read", "observe", "expect"] {
            assert!(
                session
                    .dispatch(&json!({"id": "1", "operation": operation}))
                    .is_err()
            );
        }
        assert!(
            session
                .dispatch(&json!({"id": "1", "operation": "other"}))
                .is_err()
        );
    }

    #[test]
    fn load_failure_responds_but_second_load_is_a_violation() {
        let mut session = Session::new();
        let response = session
            .dispatch(&json!({
                "id": "load", "operation": "definition.load",
                "definition_ir": "/nonexistent/krs-gate-definition-ir.json", "module": "MAIN"
            }))
            .unwrap();
        assert_eq!(response["id"], "load");
        assert!(response["error"]["message"].is_string());
        assert!(
            session
                .dispatch(&json!({"id": "2", "operation": "definition.load"}))
                .is_err()
        );
        assert!(
            session
                .dispatch(&json!({"id": "3", "operation": "execute"}))
                .is_err()
        );
    }

    #[test]
    fn rejects_kore_load_form() {
        let mut session = Session::new();
        let response = session
            .dispatch(&json!({
                "id": "load", "operation": "definition.load",
                "kore": "/nonexistent/krs-gate-definition.kore", "module": "MAIN"
            }))
            .unwrap();
        assert_eq!(
            response["error"]["message"],
            "definition.load does not accept `kore`"
        );
    }
}
