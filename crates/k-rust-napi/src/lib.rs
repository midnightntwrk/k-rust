//! Node-API bindings for the user-facing parts of the `k-rust` frontend.

use std::{collections::BTreeMap, path::Path};

use k_rust::{
    definition::checks::check_definition,
    diagnostic::{Diagnostic, Severity},
    inner::ProgramParser,
    kast::{
        json as kast_json,
        parser::{parse_sort, parse_term},
        printer::Printer as KastPrinter,
    },
    kore::{
        json as kore_json,
        parser::{parse_definition, parse_pattern},
        printer::Printer as KorePrinter,
    },
    native::embedded_builtin,
    outer::{LoadOptions, ResolvedSource, SourceResolver, load_with_options},
};
use napi::{Error, Result};
use napi_derive::napi;

#[napi(object)]
pub struct NativeSource {
    /// Stable virtual filename used for `requires` resolution and diagnostics.
    pub name: String,
    pub text: String,
}

#[napi(object)]
pub struct NativeParseProgramOptions {
    pub definition: String,
    pub module_name: String,
    pub sort: String,
    pub program: String,
    pub source_name: Option<String>,
    pub sources: Option<Vec<NativeSource>>,
    pub markdown_selector: Option<String>,
    pub include_prelude: Option<bool>,
}

#[napi(object)]
pub struct NativeDiagnostic {
    pub severity: String,
    pub code: String,
    pub message: String,
    pub source: Option<String>,
    pub start_line: Option<u32>,
    pub start_column: Option<u32>,
    pub end_line: Option<u32>,
    pub end_column: Option<u32>,
}

#[napi(object)]
pub struct NativeParsedProgram {
    /// Canonical textual KAST.
    pub text: String,
    /// KAST JSON v4 encoded as a string. The TypeScript wrapper parses this into `Kast`.
    pub json: String,
    pub diagnostics: Vec<NativeDiagnostic>,
}

#[napi(object)]
pub struct NativeSerializedTerm {
    pub text: String,
    pub json: String,
}

/// Load a K definition from virtual sources and parse one concrete program.
#[napi]
pub fn parse_program_native(options: NativeParseProgramOptions) -> Result<NativeParsedProgram> {
    let source_name = options
        .source_name
        .unwrap_or_else(|| "definition.k".to_owned());
    let mut resolver = VirtualResolver::new(options.sources.unwrap_or_default());
    let implicit_sources = if options.include_prelude.unwrap_or(true) {
        vec![
            embedded_builtin("prelude.md")
                .ok_or_else(|| Error::from_reason("embedded prelude is unavailable"))?,
        ]
    } else {
        Vec::new()
    };
    let loaded = load_with_options(
        ResolvedSource::new(source_name, options.definition),
        &options.module_name,
        &mut resolver,
        &LoadOptions {
            markdown_selector: options.markdown_selector.unwrap_or_else(|| "k".to_owned()),
            implicit_sources,
            excluded_module_attributes: Vec::new(),
        },
    )
    .map_err(napi_error)?;

    let diagnostics = check_definition(&loaded.resolved).map_err(napi_error)?;
    if diagnostics
        .iter()
        .any(|diagnostic| diagnostic.severity == Severity::Error)
    {
        return Err(Error::from_reason(format_diagnostics(&diagnostics)));
    }

    let sort = parse_sort(&options.sort).map_err(napi_error)?;
    let parser =
        ProgramParser::from_resolved(&loaded.resolved, &options.module_name).map_err(napi_error)?;
    let term = parser.parse(&sort, &options.program).map_err(napi_error)?;
    Ok(NativeParsedProgram {
        text: KastPrinter::new().print_term(&term),
        json: kast_json::to_string(&term).map_err(napi_error)?,
        diagnostics: diagnostics.into_iter().map(Into::into).collect(),
    })
}

/// Convert textual KAST into canonical text and KAST JSON v4.
#[napi]
pub fn parse_kast_native(source: String) -> Result<NativeSerializedTerm> {
    let term = parse_term(&source).map_err(napi_error)?;
    Ok(NativeSerializedTerm {
        text: KastPrinter::new().print_term(&term),
        json: kast_json::to_string(&term).map_err(napi_error)?,
    })
}

/// Convert KAST JSON v4 into canonical textual KAST.
#[napi]
pub fn print_kast_native(json: String) -> Result<String> {
    let term = kast_json::from_str(&json).map_err(napi_error)?;
    Ok(KastPrinter::new().print_term(&term))
}

/// Convert a textual KORE pattern into canonical text and KORE JSON v1.
#[napi]
pub fn parse_kore_native(source: String, width: Option<u32>) -> Result<NativeSerializedTerm> {
    let pattern = parse_pattern(&source).map_err(napi_error)?;
    Ok(NativeSerializedTerm {
        text: kore_printer(width).print_pattern(&pattern),
        json: kore_json::to_string(&pattern).map_err(napi_error)?,
    })
}

/// Convert KORE JSON v1 into canonical textual KORE.
#[napi]
pub fn print_kore_native(json: String, width: Option<u32>) -> Result<String> {
    let pattern = kore_json::from_str(&json).map_err(napi_error)?;
    Ok(kore_printer(width).print_pattern(&pattern))
}

/// Parse and consistently pretty-print a complete textual KORE definition.
#[napi]
pub fn format_kore_definition_native(source: String, width: Option<u32>) -> Result<String> {
    let definition = parse_definition(&source).map_err(napi_error)?;
    Ok(kore_printer(width).print_definition(&definition))
}

fn kore_printer(width: Option<u32>) -> KorePrinter {
    KorePrinter::pretty(width.unwrap_or(100) as usize)
}

fn napi_error(error: impl std::fmt::Display) -> Error {
    Error::from_reason(error.to_string())
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

impl From<Diagnostic> for NativeDiagnostic {
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
    fn new(sources: Vec<NativeSource>) -> Self {
        Self {
            sources: sources
                .into_iter()
                .map(|source| {
                    let name = normalize_source_name(Path::new(&source.name));
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
    ) -> std::result::Result<ResolvedSource, String> {
        let relative = Path::new(requiring_source)
            .parent()
            .map(|parent| normalize_source_name(&parent.join(required)));
        for candidate in relative.into_iter().chain([required.to_owned()]) {
            if let Some(source) = self.sources.get(&candidate) {
                return Ok(source.clone());
            }
        }
        embedded_builtin(required).ok_or_else(|| {
            format!("{required:?} was not provided in options.sources and is not a builtin")
        })
    }
}

fn normalize_source_name(path: &Path) -> String {
    path.components()
        .filter_map(|component| match component {
            std::path::Component::Normal(value) => Some(value.to_string_lossy()),
            std::path::Component::ParentDir => Some("..".into()),
            std::path::Component::CurDir => None,
            std::path::Component::RootDir => Some("/".into()),
            std::path::Component::Prefix(prefix) => Some(prefix.as_os_str().to_string_lossy()),
        })
        .collect::<Vec<_>>()
        .join("/")
}
