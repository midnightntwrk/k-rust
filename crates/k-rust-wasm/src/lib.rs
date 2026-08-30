//! WebAssembly bindings for the portable, host-independent `k-rust` frontend.

use std::{collections::BTreeMap, path::Path};

use k_rust::{
    backend::{
        Backend, BackendOptions, ExecuteRequest, ImplicationRequest, ObservedRequest,
        PatternRequest, ProveRequest, SearchPatternRequest, SearchRequest,
    },
    definition::checks::check_definition,
    diagnostic::{Diagnostic, Severity},
    inner::ProgramParser,
    kast::{
        json as kast_json,
        parser::{parse_sort, parse_term},
        printer::Printer as KastPrinter,
    },
    kompile::{CompilationBackend, CompileError, CompileOptions, compile_loaded_definition},
    kore::{
        json as kore_json,
        parser::{parse_definition, parse_pattern},
        printer::Printer as KorePrinter,
    },
    outer::{
        LoadOptions, ResolvedSource, SourceResolver, load_with_options, normalize_virtual_path,
    },
};
use serde::{Deserialize, Serialize};
use serde_json::Value;
use wasm_bindgen::prelude::*;

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct ParseProgramOptions {
    definition: String,
    module_name: String,
    sort: String,
    program: String,
    source_name: Option<String>,
    sources: Option<Vec<Source>>,
    markdown_selector: Option<String>,
    include_prelude: Option<bool>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct CompileDefinitionOptions {
    definition: String,
    module_name: String,
    backend: Option<String>,
    source_name: Option<String>,
    sources: Option<Vec<Source>>,
    markdown_selector: Option<String>,
    include_prelude: Option<bool>,
    kore_width: Option<u32>,
}

#[derive(Deserialize)]
#[serde(rename_all = "camelCase")]
struct CreateBackendOptions {
    definition_kore: String,
    module_name: String,
    smt_timeout_ms: Option<u32>,
    smt_retry_limit: Option<u32>,
}

#[derive(Deserialize)]
struct Source {
    name: String,
    text: String,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SerializedKast {
    text: String,
    kast: Value,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct SerializedKore {
    text: String,
    kore: Value,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct ParsedProgram {
    text: String,
    kast: Value,
    diagnostics: Vec<WasmDiagnostic>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct CompiledDefinition {
    definition_kore: String,
    syntax_definition_kore: String,
    macros_kore: String,
    diagnostics: Vec<WasmDiagnostic>,
}

#[derive(Serialize)]
#[serde(rename_all = "camelCase")]
struct WasmDiagnostic {
    severity: String,
    code: String,
    message: String,
    source: Option<String>,
    start_line: Option<u32>,
    start_column: Option<u32>,
    end_line: Option<u32>,
    end_column: Option<u32>,
}

/// A persistent portable backend. SMT-dependent operations report an explicit capability error.
#[wasm_bindgen]
pub struct WasmBackend {
    inner: Backend,
}

#[wasm_bindgen]
impl WasmBackend {
    #[wasm_bindgen(getter)]
    pub fn capabilities(&self) -> Result<String, JsError> {
        serialize(&self.inner.capabilities()).map_err(js_error)
    }

    pub fn execute(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<ExecuteRequest>(options).map_err(js_error)?;
        serialize(&self.inner.execute(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = executeObserved)]
    pub fn execute_observed(&mut self, options: &str) -> Result<String, JsError> {
        let request =
            serde_json::from_str::<ObservedRequest<ExecuteRequest>>(options).map_err(js_error)?;
        serialize(&self.inner.execute_observed(request).map_err(js_error)?).map_err(js_error)
    }

    pub fn search(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<SearchRequest>(options).map_err(js_error)?;
        serialize(&self.inner.search(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = searchPaths)]
    pub fn search_paths(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<SearchRequest>(options).map_err(js_error)?;
        serialize(&self.inner.search_paths(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = searchPattern)]
    pub fn search_pattern(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<SearchPatternRequest>(options).map_err(js_error)?;
        serialize(&self.inner.search_pattern(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = searchPatternPaths)]
    pub fn search_pattern_paths(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<SearchPatternRequest>(options).map_err(js_error)?;
        serialize(&self.inner.search_pattern_paths(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = searchObserved)]
    pub fn search_observed(&mut self, options: &str) -> Result<String, JsError> {
        let request =
            serde_json::from_str::<ObservedRequest<SearchRequest>>(options).map_err(js_error)?;
        serialize(&self.inner.search_observed(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = searchPathsObserved)]
    pub fn search_paths_observed(&mut self, options: &str) -> Result<String, JsError> {
        let request =
            serde_json::from_str::<ObservedRequest<SearchRequest>>(options).map_err(js_error)?;
        serialize(
            &self
                .inner
                .search_paths_observed(request)
                .map_err(js_error)?,
        )
        .map_err(js_error)
    }

    #[wasm_bindgen(js_name = searchPatternObserved)]
    pub fn search_pattern_observed(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<ObservedRequest<SearchPatternRequest>>(options)
            .map_err(js_error)?;
        serialize(
            &self
                .inner
                .search_pattern_observed(request)
                .map_err(js_error)?,
        )
        .map_err(js_error)
    }

    #[wasm_bindgen(js_name = searchPatternPathsObserved)]
    pub fn search_pattern_paths_observed(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<ObservedRequest<SearchPatternRequest>>(options)
            .map_err(js_error)?;
        serialize(
            &self
                .inner
                .search_pattern_paths_observed(request)
                .map_err(js_error)?,
        )
        .map_err(js_error)
    }

    pub fn simplify(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<PatternRequest>(options).map_err(js_error)?;
        serialize(&self.inner.simplify(request).map_err(js_error)?).map_err(js_error)
    }

    pub fn implies(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<ImplicationRequest>(options).map_err(js_error)?;
        serialize(&self.inner.implies(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = getModel)]
    pub fn get_model(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<PatternRequest>(options).map_err(js_error)?;
        serialize(&self.inner.get_model(request).map_err(js_error)?).map_err(js_error)
    }

    pub fn prove(&mut self, options: &str) -> Result<String, JsError> {
        let request = serde_json::from_str::<ProveRequest>(options).map_err(js_error)?;
        serialize(&self.inner.prove(request).map_err(js_error)?).map_err(js_error)
    }

    #[wasm_bindgen(js_name = addModule)]
    pub fn add_module(
        &mut self,
        module: &str,
        name_as_id: Option<bool>,
    ) -> Result<String, JsError> {
        self.inner
            .add_module(module, name_as_id.unwrap_or(false))
            .map_err(js_error)
    }
}

/// Create a persistent portable backend from an already compiled textual KORE definition.
#[wasm_bindgen(js_name = createBackendWasm)]
pub fn create_backend_wasm(options: &str) -> Result<WasmBackend, JsError> {
    let options: CreateBackendOptions = serde_json::from_str(options).map_err(js_error)?;
    let defaults = BackendOptions::default();
    let inner = Backend::new(
        &options.definition_kore,
        options.module_name,
        BackendOptions {
            smt_timeout_ms: options.smt_timeout_ms.unwrap_or(defaults.smt_timeout_ms),
            smt_retry_limit: options.smt_retry_limit.unwrap_or(defaults.smt_retry_limit),
        },
    )
    .map_err(js_error)?;
    Ok(WasmBackend { inner })
}

/// Compile an in-memory K definition and immediately create its portable backend.
#[wasm_bindgen(js_name = compileBackendWasm)]
pub fn compile_backend_wasm(options: &str) -> Result<WasmBackend, JsError> {
    let module_name = serde_json::from_str::<CompileDefinitionOptions>(options)
        .map_err(js_error)?
        .module_name;
    let compiled = compile_definition(options).map_err(js_error)?;
    let compiled: Value = serde_json::from_str(&compiled).map_err(js_error)?;
    let definition_kore = compiled
        .get("definitionKore")
        .and_then(Value::as_str)
        .ok_or_else(|| JsError::new("compiler output did not contain definitionKore"))?;
    let inner =
        Backend::new(definition_kore, module_name, BackendOptions::default()).map_err(js_error)?;
    Ok(WasmBackend { inner })
}

/// Compile an in-memory K definition into backend-facing KORE artifacts.
#[wasm_bindgen(js_name = compileDefinitionWasm)]
pub fn compile_definition_wasm(options: &str) -> Result<String, JsError> {
    compile_definition(options).map_err(js_error)
}

fn compile_definition(options: &str) -> Result<String, String> {
    let options: CompileDefinitionOptions = serde_json::from_str(options).map_err(display_error)?;
    let backend = options
        .backend
        .as_deref()
        .unwrap_or("rust")
        .parse::<CompilationBackend>()?;
    if options.include_prelude.unwrap_or(false) {
        return Err(
            "the embedded prelude requires native Z3 inference and is unavailable in WebAssembly; provide portable sources explicitly"
                .to_owned(),
        );
    }
    let source_name = options
        .source_name
        .unwrap_or_else(|| "definition.k".to_owned());
    let mut resolver = VirtualResolver::new(options.sources.unwrap_or_default());
    let loaded = load_with_options(
        ResolvedSource::new(source_name, options.definition),
        &options.module_name,
        &mut resolver,
        &LoadOptions {
            markdown_selector: options.markdown_selector.unwrap_or_else(|| "k".to_owned()),
            implicit_sources: Vec::new(),
            excluded_module_attributes: vec![backend.excluded_module_attribute().to_owned()],
            configuration_module: None,
        },
    )
    .map_err(display_error)?;
    let artifacts = compile_loaded_definition(
        &loaded,
        CompileOptions {
            backend,
            kore_width: options.kore_width.unwrap_or(100) as usize,
            ..CompileOptions::default()
        },
    )
    .map_err(format_compile_error)?;
    serialize(&CompiledDefinition {
        definition_kore: artifacts.definition_kore,
        syntax_definition_kore: artifacts.syntax_definition_kore,
        macros_kore: artifacts.macros_kore,
        diagnostics: artifacts.diagnostics.into_iter().map(Into::into).collect(),
    })
}

/// Load an in-memory K definition and parse one concrete program.
#[wasm_bindgen(js_name = parseProgramWasm)]
pub fn parse_program_wasm(options: &str) -> Result<String, JsError> {
    parse_program(options).map_err(js_error)
}

fn parse_program(options: &str) -> Result<String, String> {
    let options: ParseProgramOptions = serde_json::from_str(options).map_err(display_error)?;
    let source_name = options
        .source_name
        .unwrap_or_else(|| "definition.k".to_owned());
    let mut resolver = VirtualResolver::new(options.sources.unwrap_or_default());
    if options.include_prelude.unwrap_or(false) {
        return Err(
            "the embedded prelude requires native Z3 inference and is unavailable in WebAssembly; provide portable sources explicitly"
                .to_owned(),
        );
    }
    let loaded = load_with_options(
        ResolvedSource::new(source_name, options.definition),
        &options.module_name,
        &mut resolver,
        &LoadOptions {
            markdown_selector: options.markdown_selector.unwrap_or_else(|| "k".to_owned()),
            implicit_sources: Vec::new(),
            excluded_module_attributes: Vec::new(),
            configuration_module: None,
        },
    )
    .map_err(display_error)?;

    let diagnostics = check_definition(&loaded.resolved).map_err(display_error)?;
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(format_diagnostics(&diagnostics));
    }

    let sort = parse_sort(&options.sort).map_err(display_error)?;
    let parser = ProgramParser::from_resolved(&loaded.resolved, &options.module_name)
        .map_err(display_error)?;
    let term = parser
        .parse(&sort, &options.program)
        .map_err(display_error)?;
    serialize(&ParsedProgram {
        text: KastPrinter::new().print_term(&term),
        kast: json_value(kast_json::to_string(&term).map_err(display_error)?)?,
        diagnostics: diagnostics.into_iter().map(Into::into).collect(),
    })
}

/// Convert textual KAST into canonical text and KAST JSON v4.
#[wasm_bindgen(js_name = parseKastWasm)]
pub fn parse_kast_wasm(source: &str) -> Result<String, JsError> {
    parse_kast(source).map_err(js_error)
}

fn parse_kast(source: &str) -> Result<String, String> {
    let term = parse_term(source).map_err(display_error)?;
    serialize(&SerializedKast {
        text: KastPrinter::new().print_term(&term),
        kast: json_value(kast_json::to_string(&term).map_err(display_error)?)?,
    })
}

/// Convert KAST JSON v4 into canonical textual KAST.
#[wasm_bindgen(js_name = printKastWasm)]
pub fn print_kast_wasm(json: &str) -> Result<String, JsError> {
    let term = kast_json::from_str(json).map_err(js_error)?;
    Ok(KastPrinter::new().print_term(&term))
}

/// Convert a textual KORE pattern into canonical text and KORE JSON v1.
#[wasm_bindgen(js_name = parseKoreWasm)]
pub fn parse_kore_wasm(source: &str, width: Option<u32>) -> Result<String, JsError> {
    parse_kore(source, width).map_err(js_error)
}

fn parse_kore(source: &str, width: Option<u32>) -> Result<String, String> {
    let pattern = parse_pattern(source).map_err(display_error)?;
    serialize(&SerializedKore {
        text: kore_printer(width).print_pattern(&pattern),
        kore: kore_json::to_value(&pattern).map_err(display_error)?,
    })
}

/// Convert KORE JSON v1 into canonical textual KORE.
#[wasm_bindgen(js_name = printKoreWasm)]
pub fn print_kore_wasm(json: &str, width: Option<u32>) -> Result<String, JsError> {
    print_kore(json, width).map_err(js_error)
}

fn print_kore(json: &str, width: Option<u32>) -> Result<String, String> {
    let pattern = kore_json::from_str_unbounded(json).map_err(display_error)?;
    Ok(kore_printer(width).print_pattern(&pattern))
}

/// Parse and consistently pretty-print a complete textual KORE definition.
#[wasm_bindgen(js_name = formatKoreDefinitionWasm)]
pub fn format_kore_definition_wasm(source: &str, width: Option<u32>) -> Result<String, JsError> {
    let definition = parse_definition(source).map_err(js_error)?;
    Ok(kore_printer(width).print_definition(&definition))
}

fn kore_printer(width: Option<u32>) -> KorePrinter {
    KorePrinter::pretty(width.unwrap_or(100) as usize)
}

fn serialize(value: &impl Serialize) -> Result<String, String> {
    serde_json::to_string(value).map_err(display_error)
}

fn json_value(json: String) -> Result<Value, String> {
    let mut deserializer = serde_json::Deserializer::from_str(&json);
    deserializer.disable_recursion_limit();
    let value = Value::deserialize(&mut deserializer).map_err(display_error)?;
    deserializer.end().map_err(display_error)?;
    Ok(value)
}

fn display_error(error: impl std::fmt::Display) -> String {
    error.to_string()
}

fn js_error(error: impl std::fmt::Display) -> JsError {
    JsError::new(&error.to_string())
}

fn format_compile_error(error: CompileError) -> String {
    let diagnostics = format_diagnostics(&error.diagnostics);
    if diagnostics.is_empty() {
        error.to_string()
    } else {
        format!("{error}\n{diagnostics}")
    }
}

fn format_diagnostics(diagnostics: &[Diagnostic]) -> String {
    diagnostics
        .iter()
        .filter(|diagnostic| diagnostic.severity == Severity::Error)
        .map(|diagnostic| {
            let location = match (&diagnostic.source, diagnostic.location) {
                (Some(source), Some(location)) => format!(
                    "{source}:{}:{}: ",
                    location.start_line, location.start_column
                ),
                (Some(source), None) => format!("{source}: "),
                _ => String::new(),
            };
            format!("{location}{:?}: {}", diagnostic.code, diagnostic.message)
        })
        .collect::<Vec<_>>()
        .join("\n")
}

impl From<Diagnostic> for WasmDiagnostic {
    fn from(diagnostic: Diagnostic) -> Self {
        let (start_line, start_column, end_line, end_column) = diagnostic
            .location
            .map(|location| {
                (
                    Some(location.start_line),
                    Some(location.start_column),
                    Some(location.end_line),
                    Some(location.end_column),
                )
            })
            .unwrap_or((None, None, None, None));
        Self {
            severity: format!("{:?}", diagnostic.severity).to_lowercase(),
            code: format!("{:?}", diagnostic.code),
            message: diagnostic.message,
            source: diagnostic.source,
            start_line,
            start_column,
            end_line,
            end_column,
        }
    }
}

struct VirtualResolver {
    sources: BTreeMap<String, ResolvedSource>,
}

impl VirtualResolver {
    fn new(sources: Vec<Source>) -> Self {
        Self {
            sources: sources
                .into_iter()
                .map(|source| {
                    let name = normalize_virtual_path(Path::new(&source.name));
                    (name.clone(), ResolvedSource::new(name, source.text))
                })
                .collect(),
        }
    }
}

impl SourceResolver for VirtualResolver {
    fn resolve(
        &mut self,
        requiring_source: &str,
        required: &str,
    ) -> Result<ResolvedSource, String> {
        let relative = Path::new(requiring_source)
            .parent()
            .map(|parent| normalize_virtual_path(&parent.join(required)));
        for candidate in relative.into_iter().chain([required.to_owned()]) {
            if let Some(source) = self.sources.get(&candidate) {
                return Ok(source.clone());
            }
        }
        Err(format!("{required:?} was not provided in options.sources"))
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn deeply_nested_kore_json(depth: usize) -> String {
        let sort = r#"{"tag":"SortApp","name":"SortK","args":[]}"#;
        let mut term = format!(r#"{{"tag":"Top","sort":{sort}}}"#);
        for _ in 0..depth {
            term = format!(r#"{{"tag":"Not","sort":{sort},"arg":{term}}}"#);
        }
        format!(r#"{{"format":"KORE","version":1,"term":{term}}}"#)
    }

    #[test]
    fn converts_deep_serialized_values_without_the_default_json_recursion_limit() {
        let mut json = "null".to_owned();
        for _ in 0..160 {
            json = format!("[{json}]");
        }

        assert!(json_value(json).is_ok());
    }

    #[test]
    fn prints_deep_kore_json_without_the_default_recursion_limit() {
        std::thread::Builder::new()
            .stack_size(16 * 1024 * 1024)
            .spawn(|| assert!(print_kore(&deeply_nested_kore_json(160), None).is_ok()))
            .unwrap()
            .join()
            .unwrap();
    }

    #[test]
    fn serializes_portable_kast_and_kore_results() {
        assert!(
            parse_kast(r#"#token("x","Id")"#)
                .unwrap()
                .contains("KToken")
        );
        assert!(parse_kore("X:S", None).unwrap().contains("EVar"));
    }

    #[test]
    fn parses_programs_through_virtual_requires() {
        let result = parse_program(
            r#"{
                "definition": "requires \"../base.k\"\nmodule MAIN\n imports BASE\n syntax Exp ::= Int\nendmodule",
                "moduleName": "MAIN",
                "sort": "Exp",
                "program": "42",
                "sourceName": "definitions/nested/main.k",
                "sources": [{
                    "name": "definitions/base.k",
                    "text": "module BASE\n syntax Int ::= r\"[0-9]+\" [token]\nendmodule"
                }],
                "includePrelude": false
            }"#,
        )
        .unwrap();
        assert!(result.contains(r#"#token(\"42\",\"Int\")"#));
    }

    #[test]
    fn compiles_a_portable_definition() {
        let result = compile_definition(
            r#"{
                "definition": "module MAIN\n syntax Int ::= r\"[0-9]+\" [token]\n syntax Exp ::= Int\nendmodule",
                "moduleName": "MAIN",
                "includePrelude": false
            }"#,
        )
        .unwrap();
        assert!(result.contains("definitionKore"));
        assert!(result.contains("module MAIN"));
    }
}
