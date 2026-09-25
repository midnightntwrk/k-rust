//! Persistent newline-delimited JSON driver for the pinned in-process K backend.

use k_rust::{
    backend::{Backend, BackendOptions, ExecuteRequest, ProveRequest},
    kore::{json as kore_json, parser::parse_pattern},
};
use serde::Deserialize;
use serde_json::{Value, json};
use std::{
    env,
    error::Error,
    fs,
    io::{self, BufRead, Write},
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

fn run() -> Result<(), Box<dyn Error>> {
    let mut arguments = env::args_os().skip(1);
    let definition_path = arguments
        .next()
        .ok_or("usage: krs-native-runner DEFINITION MODULE")?;
    let module = arguments
        .next()
        .ok_or("usage: krs-native-runner DEFINITION MODULE")?;
    if arguments.next().is_some() {
        return Err("usage: krs-native-runner DEFINITION MODULE".into());
    }
    let module = module
        .into_string()
        .map_err(|_| "backend module name must be UTF-8")?;
    let definition = fs::read_to_string(definition_path)?;
    let mut backend = Backend::new(&definition, module, BackendOptions::default())?;
    let stdin = io::stdin();
    let mut stdout = io::BufWriter::new(io::stdout().lock());
    for line in stdin.lock().lines() {
        let request: Value = serde_json::from_str(&line?)?;
        let id = required_string(&request, "id")?;
        let result = match required_string(&request, "operation")? {
            "execute" => execute(&mut backend, &request)?,
            "prove" => prove(&mut backend, &request)?,
            operation => return Err(format!("unsupported operation `{operation}`").into()),
        };
        serde_json::to_writer(&mut stdout, &json!({"id": id, "result": result}))?;
        stdout.write_all(b"\n")?;
        stdout.flush()?;
    }
    Ok(())
}

fn main() -> Result<(), Box<dyn Error>> {
    let result = std::thread::Builder::new()
        .name("krs-native-backend".into())
        .stack_size(64 * 1024 * 1024)
        .spawn(|| run().map_err(|error| error.to_string()))?
        .join()
        .map_err(|_| "native backend thread panicked")?;
    result.map_err(Into::into)
}
