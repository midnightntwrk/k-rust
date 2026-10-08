//! Newline-delimited JSON native backend session.

use crate::{
    compile::read_ir,
    kore_digest,
    pattern::{self, PatternContext},
};
use k_rust::{
    backend::{Backend, ExecuteRequest, ProveRequest, SearchRequest},
    kore::{
        ast::Pattern,
        json as kore_json,
        parser::{parse_definition, parse_pattern},
    },
};
use krs_exec::{
    ConfigInputs, ProgramInput, ProveOptions, RunOptions, SearchMode, SearchOptions, Semantics,
};
use krs_ir::measure::Timings;
use serde::Deserialize;
use serde_json::{Value, json};
use sha2::{Digest, Sha256};
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
    let mut execute = ExecuteRequest::new(parse_pattern(required_string(request, "pattern")?)?);
    execute.max_depth = max_depth;
    if let Some(value) = request.get("max_simplification_iterations") {
        execute.max_simplification_iterations =
            usize::try_from(value.as_u64().ok_or(
                "request field `max_simplification_iterations` must be an unsigned integer",
            )?)?;
    }
    let mut result = backend.execute(execute)?;
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

/// A search result and the states a `keep` or `keep_each` request retains.
type SearchOutcome = (Value, Option<Vec<Pattern>>);

fn search(backend: &mut Backend, request: &Value) -> Result<SearchOutcome, Box<dyn Error>> {
    let limit = |key: &str| -> Result<Option<u64>, Box<dyn Error>> {
        match request.get(key) {
            None | Some(Value::Null) => Ok(None),
            Some(value) => Ok(Some(value.as_u64().ok_or_else(|| {
                format!("request field `{key}` must be an unsigned integer or null")
            })?)),
        }
    };
    let mut search = SearchRequest::new(parse_pattern(required_string(request, "pattern")?)?);
    search.max_depth = limit("max_depth")?;
    search.max_results = limit("max_results")?.map(usize::try_from).transpose()?;
    let result = backend.search(search)?;
    if request.get("keep_each").is_some() {
        let mut retained = Vec::with_capacity(result.states.len());
        for state in &result.states {
            let source = serde_json::to_string(&state.state)?;
            retained.push(kore_json::from_str(&source)?);
        }
        return Ok((
            json!({"modality": result.modality, "states": result.states.len()}),
            Some(retained),
        ));
    }
    if request.get("keep").is_some() {
        if result.states.len() != 1 {
            return Err(format!(
                "search with `keep` requires exactly one result state, got {}",
                result.states.len()
            )
            .into());
        }
        let source = serde_json::to_string(&result.states[0].state)?;
        let retained = kore_json::from_str(&source)?;
        Ok((
            json!({"modality": result.modality, "states": result.states.len()}),
            Some(vec![retained]),
        ))
    } else {
        Ok((serde_json::to_value(result)?, None))
    }
}

fn optional_u64(request: &Value, key: &str) -> Result<Option<u64>, Box<dyn Error>> {
    match request.get(key) {
        None | Some(Value::Null) => Ok(None),
        Some(value) => Ok(Some(value.as_u64().ok_or_else(|| {
            format!("request field `{key}` must be an unsigned integer or null")
        })?)),
    }
}

/// The `krs run` inputs of an `exec.*` request: `program` (text) with optional `program_name`, and `variables` (an object of `-c` bindings).
fn printed_value(printed: &krs_exec::Printed) -> Value {
    json!({
        "text": printed.text,
        "warnings": printed.warnings.iter().map(ToString::to_string).collect::<Vec<_>>(),
    })
}

fn config_inputs(request: &Value) -> Result<ConfigInputs, Box<dyn Error>> {
    let program = match request.get("program") {
        None | Some(Value::Null) => None,
        Some(value) => Some(ProgramInput {
            name: request
                .get("program_name")
                .and_then(Value::as_str)
                .unwrap_or("<program>")
                .to_owned(),
            text: value
                .as_str()
                .ok_or("request field `program` must be a string")?
                .to_owned(),
        }),
    };
    let variables = match request.get("variables") {
        None | Some(Value::Null) => Vec::new(),
        Some(value) => value
            .as_object()
            .ok_or("request field `variables` must be an object")?
            .iter()
            .map(|(name, text)| {
                text.as_str()
                    .map(|text| (name.clone(), text.to_owned()))
                    .ok_or_else(|| format!("variable `{name}` must be surface text"))
            })
            .collect::<Result<_, _>>()?,
    };
    Ok(ConfigInputs { program, variables })
}

/// A session with at most one loaded definition.
#[derive(Default)]
pub struct Session {
    semantics: Option<Semantics>,
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
                | "search"
                | "prove"
                | "exec.run"
                | "exec.search"
                | "exec.prove"
                | "term.unparse"
                | "kore.read"
                | "kore.digest"
                | "kore.attributes"
                | "ir.query"
                | "registration.table"
                | "kast.normalize"
                | "kast.project"
                | "kast.frontier"
                | "kast.inspect"
                | "observe"
                | "expect"
        ) {
            return Err(format!("unsupported operation `{operation}`").into());
        }
        if self.semantics.is_none()
            && !matches!(
                operation,
                "definition.load"
                    | "kore.digest"
                    | "kore.attributes"
                    | "ir.query"
                    | "registration.table"
                    | "kast.normalize"
                    | "kast.project"
                    | "kast.frontier"
                    | "kast.inspect"
            )
        {
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
            "search" => self.search(request),
            "prove" => prove(self.backend()?, request),
            "exec.run" => self.exec_run(request),
            "exec.search" => self.exec_search(request),
            "exec.prove" => self.exec_prove(request),
            "term.unparse" => self.unparse(request),
            "kore.read" => self.read(request),
            "kore.digest" => Self::digest(request),
            "kore.attributes" => Self::attributes(request),
            "ir.query" => crate::ir_query::dispatch(request),
            "registration.table" => crate::registration::dispatch(request),
            "kast.normalize" | "kast.project" | "kast.frontier" | "kast.inspect" => {
                crate::kast::dispatch(operation, request).map_err(Into::into)
            }
            "observe" => self.observe(request),
            "expect" => self.expect(request),
            _ => unreachable!("validated operation"),
        };
        Ok(match result {
            Ok(value) => json!({"id": id, "result": value}),
            Err(error) => json!({"id": id, "error": {"message": error.to_string()}}),
        })
    }

    fn backend(&mut self) -> Result<&mut Backend, Box<dyn Error>> {
        Ok(self
            .semantics
            .as_mut()
            .ok_or("backend not loaded")?
            .backend_mut())
    }

    fn semantics(&mut self) -> Result<&mut Semantics, Box<dyn Error>> {
        Ok(self.semantics.as_mut().ok_or("definition not loaded")?)
    }

    fn load(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let module = required_string(request, "module")?;
        if request.get("kore").is_some() {
            return Err("definition.load does not accept `kore`".into());
        }
        let path = required_string(request, "definition_ir")?;
        let mut timings = Timings::disabled();
        let definition_ir = read_ir(&mut timings, Path::new(path))?;
        let semantics = Semantics::compile_with(&definition_ir, None, &mut timings).map_err(
            |error| match error {
                krs_exec::ExecError::Compile(error) => format!("{error:#?}"),
                error => error.to_string(),
            },
        )?;
        if semantics.main_module() != module {
            return Err(format!(
                "Definition IR main module is `{}`, not requested `{module}`",
                semantics.main_module()
            )
            .into());
        }
        let patterns =
            PatternContext::from_definition(&parse_definition(semantics.definition_kore())?)?
                .with_frontend_cells(semantics.frontend_definition())?;
        let digest = format!(
            "{:x}",
            Sha256::digest(semantics.definition_kore().as_bytes())
        );
        self.semantics = Some(semantics);
        self.patterns = Some(patterns);
        Ok(json!({
            "module": module,
            "definition_kore_sha256": digest,
        }))
    }

    fn configure(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let variables = request
            .get("variables")
            .and_then(Value::as_object)
            .ok_or("request field `variables` must be an object")?;
        self.semantics()?.configuration_mut().configure(variables)
    }

    /// `krs run` through `krs-exec`: configure from `program` and `variables`, then run with `depth` and `trace`.
    fn exec_run(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let inputs = config_inputs(request)?;
        let options = RunOptions {
            depth: optional_u64(request, "depth")?,
            trace: request
                .get("trace")
                .and_then(Value::as_bool)
                .unwrap_or(false),
        };
        let pretty = match request.get("print") {
            None | Some(Value::Null) => false,
            Some(Value::String(style)) if style == "pretty" => true,
            Some(other) => {
                return Err(
                    format!("request field `print` must be \"pretty\", not {other}").into(),
                );
            }
        };
        let semantics = self.semantics()?;
        let state = semantics.configure(&inputs)?;
        let report = semantics.run(&state, options)?;
        let mut value = serde_json::to_value(&report)?;
        if pretty {
            value["printed"] = printed_value(&semantics.unparse(&report.state, false));
        }
        Ok(value)
    }

    /// `krs parse --output program` (`mode` `"program"`, with `program` text and an optional `sort`),
    /// or `--output pretty` of a KORE pattern (`mode` `"pretty"`, with `kore` text).
    fn unparse(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let color = request
            .get("color")
            .and_then(Value::as_bool)
            .unwrap_or(false);
        let semantics = self.semantics()?;
        let printed = match required_string(request, "mode")? {
            "program" => {
                let input = ProgramInput {
                    name: request
                        .get("program_name")
                        .and_then(Value::as_str)
                        .unwrap_or("<program>")
                        .to_owned(),
                    text: required_string(request, "program")?.to_owned(),
                };
                let sort = request.get("sort").and_then(Value::as_str);
                semantics.unparse_program(sort, &input, color)?
            }
            "pretty" => {
                let pattern = parse_pattern(required_string(request, "kore")?)?;
                let term = krs_exec::Term::from_kore(pattern)?;
                semantics.unparse(&term, color)
            }
            other => return Err(format!("unknown unparse mode `{other}`").into()),
        };
        Ok(printed_value(&printed))
    }

    /// `krs search` through `krs-exec`.
    fn exec_search(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let inputs = config_inputs(request)?;
        let mode = match request.get("mode") {
            None | Some(Value::Null) => SearchMode::Final,
            Some(value) => {
                let name = value
                    .as_str()
                    .ok_or("request field `mode` must be a string")?;
                SearchMode::ALL
                    .into_iter()
                    .find(|mode| mode.as_str() == name)
                    .ok_or_else(|| format!("unknown search mode `{name}`"))?
            }
        };
        let options = SearchOptions {
            mode,
            depth: optional_u64(request, "depth")?,
            max_solutions: optional_u64(request, "max_solutions")?
                .map(usize::try_from)
                .transpose()?,
            trace: request
                .get("trace")
                .and_then(Value::as_bool)
                .unwrap_or(false),
        };
        let semantics = self.semantics()?;
        let state = semantics.configure(&inputs)?;
        Ok(serde_json::to_value(semantics.search(&state, options)?)?)
    }

    /// `krs prove` through `krs-exec`: `claims` (labels; empty proves every claim) and `depth`.
    fn exec_prove(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let claims = match request.get("claims") {
            None | Some(Value::Null) => Vec::new(),
            Some(value) => value
                .as_array()
                .ok_or("request field `claims` must be an array")?
                .iter()
                .map(|label| {
                    label
                        .as_str()
                        .map(str::to_owned)
                        .ok_or("claim labels must be strings")
                })
                .collect::<Result<_, _>>()?,
        };
        let options = ProveOptions {
            module: None,
            claims,
            depth: optional_u64(request, "depth")?,
        };
        Ok(serde_json::to_value(self.semantics()?.prove(&options)?)?)
    }

    fn execute(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let keep = request
            .get("keep")
            .map(|_| required_string(request, "keep"))
            .transpose()?;
        let (result, state) = execute(self.backend()?, request)?;
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

    fn search(&mut self, request: &Value) -> Result<Value, Box<dyn Error>> {
        let keep = request
            .get("keep")
            .map(|_| required_string(request, "keep"))
            .transpose()?
            .map(str::to_owned);
        let keep_each = request
            .get("keep_each")
            .map(|_| required_string(request, "keep_each"))
            .transpose()?
            .map(str::to_owned);
        if keep.is_some() && keep_each.is_some() {
            return Err("search accepts `keep` or `keep_each`, not both".into());
        }
        let (result, states) = search(self.backend()?, request)?;
        if let Some(states) = states {
            if let Some(name) = keep {
                self.states
                    .insert(name, states.into_iter().next().expect("one kept state"));
            } else if let Some(prefix) = keep_each {
                for (index, state) in states.into_iter().enumerate() {
                    self.states.insert(format!("{prefix}{index}"), state);
                }
            }
        }
        Ok(result)
    }

    fn digest(request: &Value) -> Result<Value, Box<dyn Error>> {
        let kore = Path::new(required_string(request, "kore")?);
        let semantics = Path::new(required_string(request, "semantics")?);
        Ok(json!({"sha256": kore_digest::digest_file(kore, semantics)?}))
    }

    fn attributes(request: &Value) -> Result<Value, Box<dyn Error>> {
        let kore = Path::new(required_string(request, "kore")?);
        let strings = |field: &str| -> Result<Vec<String>, Box<dyn Error>> {
            request
                .get(field)
                .and_then(Value::as_array)
                .ok_or_else(|| format!("request field `{field}` must be an array"))?
                .iter()
                .map(|value| {
                    value.as_str().map(str::to_owned).ok_or_else(|| {
                        format!("request field `{field}` must contain strings").into()
                    })
                })
                .collect()
        };
        let symbols = crate::kore_attributes::symbol_attributes(
            kore,
            &strings("labels")?,
            &strings("attributes")?,
        )?;
        Ok(json!({"symbols": symbols}))
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
        let configuration = self.semantics()?.configuration_mut();
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
        let line = line?;
        let mut decoder = serde_json::Deserializer::from_str(&line);
        decoder.disable_recursion_limit();
        let request = Value::deserialize(&mut decoder)?;
        decoder.end()?;
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
    use super::{Session, search};
    use k_rust::{
        backend::{Backend, BackendOptions},
        kore::parser::parse_pattern,
    };
    use serde_json::json;

    fn search_backend() -> Backend {
        let definition = r#"[]
            module MAIN
                sort SortState{} []
                symbol initial{}() : SortState{} [constructor{}()]
                symbol left{}() : SortState{} [constructor{}()]
                symbol right{}() : SortState{} [constructor{}()]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(initial{}(), \top{SortState{}}()), left{}()
                ) [label{}("left")]
                axiom{} \rewrites{SortState{}}(
                    \and{SortState{}}(initial{}(), \top{SortState{}}()), right{}()
                ) [label{}("right")]
            endmodule []"#;
        Backend::new(definition, "MAIN", BackendOptions::default()).unwrap()
    }

    #[test]
    fn search_returns_final_states_and_retains_a_single_result() {
        let mut backend = search_backend();
        let (result, retained) = search(
            &mut backend,
            &json!({
                "id": "raw", "operation": "search", "pattern": "initial{}()",
                "max_depth": null, "max_results": null
            }),
        )
        .unwrap();
        assert_eq!(result["states"].as_array().unwrap().len(), 2);
        assert!(retained.is_none());

        for (pattern, expected) in [("left{}()", "left{}()"), ("right{}()", "right{}()")] {
            let (result, retained) = search(
                &mut backend,
                &json!({
                    "id": "retained", "operation": "search", "pattern": pattern,
                    "max_depth": 1, "max_results": 1, "keep": "final"
                }),
            )
            .unwrap();
            assert_eq!(result["states"], 1);
            assert!(result["modality"].is_string());
            assert_eq!(result.as_object().unwrap().len(), 2);
            assert_eq!(retained.unwrap(), [parse_pattern(expected).unwrap()]);
        }

        let (result, retained) = search(
            &mut backend,
            &json!({
                "id": "each", "operation": "search", "pattern": "initial{}()",
                "keep_each": "final#"
            }),
        )
        .unwrap();
        assert_eq!(result["states"], 2);
        let mut retained = retained.unwrap();
        retained.sort_by_key(ToString::to_string);
        assert_eq!(
            retained,
            [
                parse_pattern("left{}()").unwrap(),
                parse_pattern("right{}()").unwrap()
            ]
        );
    }

    #[test]
    fn failed_search_reports_each_invalid_request() {
        let mut backend = search_backend();
        for (max_results, count) in [(json!(null), 2), (json!(0), 0)] {
            let error = search(
                &mut backend,
                &json!({
                    "id": "multiple", "operation": "search", "pattern": "initial{}()",
                    "max_results": max_results, "keep": "final"
                }),
            )
            .unwrap_err();
            assert_eq!(
                error.to_string(),
                format!("search with `keep` requires exactly one result state, got {count}")
            );
        }
        for (field, value) in [("max_depth", json!(-1)), ("max_results", json!("1"))] {
            let mut request = json!({
                "id": "invalid", "operation": "search", "pattern": "left{}()"
            });
            request[field] = value;
            assert!(search(&mut backend, &request).is_err());
        }
        let (result, _) = search(
            &mut backend,
            &json!({"id": "valid", "operation": "search", "pattern": "left{}()"}),
        )
        .unwrap();
        assert_eq!(result["states"].as_array().unwrap().len(), 1);
    }

    #[test]
    fn artifact_queries_are_independent_and_failures_keep_the_session_open() {
        let mut session = Session::new();
        for query in [
            json!({"id":"query","operation":"ir.query","artifacts":"missing","query":{"kind":"files"}}),
            json!({"id":"missing-path","operation":"ir.query","query":{"kind":"files"}}),
            json!({"id":"missing-query","operation":"ir.query","artifacts":"missing"}),
        ] {
            let response = session.dispatch(&query).unwrap();
            assert_eq!(response["id"], query["id"]);
            assert!(response.get("error").is_some());
            assert!(!session.load_attempted);
        }
    }

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
        let attributes = session
            .dispatch(&json!({
                "id": "attributes", "operation": "kore.attributes",
                "kore": "/nonexistent/krs-gate-definition.kore",
                "labels": ["while"], "attributes": ["format"]
            }))
            .unwrap();
        assert!(attributes["error"]["message"].is_string());
        let malformed = session
            .dispatch(&json!({
                "id": "malformed", "operation": "kore.attributes",
                "kore": "/nonexistent/krs-gate-definition.kore", "labels": "while"
            }))
            .unwrap();
        assert_eq!(
            malformed["error"]["message"],
            "request field `labels` must be an array"
        );
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
        for operation in ["search", "kore.read", "observe", "expect"] {
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
