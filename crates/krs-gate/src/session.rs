//! Newline-delimited JSON native backend session.

use crate::{compile::compile_ir, configuration::Configuration};
use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ProveRequest},
    kore::{json as kore_json, parser::parse_pattern},
};
use krs_ir::measure::Timings;
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
    error::Error,
    fs,
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

fn execute(backend: &mut Backend, request: &Value) -> Result<Value, Box<dyn Error>> {
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
    Ok(serde_json::to_value(result)?)
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
            "definition.load" | "configure" | "execute" | "prove"
        ) {
            return Err(format!("unsupported operation `{operation}`").into());
        }
        if self.backend.is_none() && operation != "definition.load" {
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
            "execute" => execute(self.backend.as_mut().ok_or("backend not loaded")?, request),
            "prove" => prove(self.backend.as_mut().ok_or("backend not loaded")?, request),
            _ => unreachable!("validated operation"),
        };
        Ok(match result {
            Ok(value) => json!({"id": id, "result": value}),
            Err(error) => json!({"id": id, "error": {"message": error.to_string()}}),
        })
    }

    fn load(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let module = required_string(request, "module")?;
        let (definition, configuration) = match (request.get("definition_ir"), request.get("kore"))
        {
            (Some(Value::String(path)), None) => {
                let (artifacts, context) = compile_ir(&mut Timings::disabled(), Path::new(path))?;
                if context.frontend_definition.main_module != module {
                    return Err(format!(
                        "Definition IR main module is `{}`, not requested `{module}`",
                        context.frontend_definition.main_module
                    )
                    .into());
                }
                (
                    artifacts.definition_kore,
                    Some(Configuration::new(context)?),
                )
            }
            (None, Some(Value::String(path))) => (fs::read_to_string(path)?, None),
            _ => {
                return Err(
                    "definition.load requires exactly one string `definition_ir` or `kore`".into(),
                );
            }
        };
        self.backend = Some(Backend::new(
            &definition,
            module.to_owned(),
            BackendOptions::default(),
        )?);
        self.configuration = configuration;
        Ok(json!({"module": module}))
    }

    fn configure(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let variables = request
            .get("variables")
            .and_then(Value::as_object)
            .ok_or("request field `variables` must be an object")?;
        self.configuration
            .as_mut()
            .ok_or("configure requires definition_ir loading")?
            .configure(variables)
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
                "kore": "/nonexistent/krs-gate-definition.kore", "module": "MAIN"
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
}
