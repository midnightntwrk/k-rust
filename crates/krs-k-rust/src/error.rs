use std::{error::Error, fmt};

use k_rust::{
    diagnostic::{
        Diagnostic as NativeDiagnostic, DiagnosticCode as NativeDiagnosticCode,
        Severity as NativeSeverity,
    },
    kompile,
};
use krs_diagnostic::{
    Code, Diagnostic, Label, Location, Severity, ToDiagnostic, codes,
    envelope::DiagnosticGeneratedRange,
};
use krs_ir::SourceMapKey;

use crate::{
    InputAddress, InputSpace,
    adapter::{AdapterError, NativeNodePlace, OriginMapping, SentenceNodeRole},
    provenance::ProvenanceError,
};

/// Severity of a native frontend diagnostic.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DiagnosticSeverity {
    /// The frontend rejected the definition.
    Error,
    /// The frontend accepted the definition with a warning.
    Warning,
}

impl From<DiagnosticSeverity> for Severity {
    fn from(severity: DiagnosticSeverity) -> Self {
        match severity {
            DiagnosticSeverity::Error => Self::Error,
            DiagnosticSeverity::Warning => Self::Warning,
        }
    }
}

impl From<NativeSeverity> for DiagnosticSeverity {
    fn from(severity: NativeSeverity) -> Self {
        match severity {
            NativeSeverity::Error => Self::Error,
            NativeSeverity::Warning => Self::Warning,
        }
    }
}

/// One-based source location reported by the native frontend.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct SourceLocation {
    /// First source line.
    pub start_line: u32,
    /// First source column.
    pub start_column: u32,
    /// Last source line.
    pub end_line: u32,
    /// Last source column.
    pub end_column: u32,
}

/// Renderer-independent diagnostic returned by the pinned frontend.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct FrontendDiagnostic {
    /// Diagnostic severity.
    pub severity: DiagnosticSeverity,
    /// Stable-within-the-pin native diagnostic code name.
    pub code: Code,
    /// Human-readable diagnostic message.
    pub message: String,
    /// Source identifier, when attached to the originating sentence.
    pub source: Option<String>,
    /// Source location, when attached to the originating sentence.
    pub location: Option<SourceLocation>,
    /// Exact adapted Definition source-map key, when a structured address resolves.
    pub source_map_key: Option<SourceMapKey>,
    /// Input sentence addresses attached by the native frontend.
    pub input_addresses: Vec<InputAddress>,
}

impl From<&NativeDiagnostic> for FrontendDiagnostic {
    fn from(diagnostic: &NativeDiagnostic) -> Self {
        Self {
            severity: diagnostic.severity.into(),
            code: native_diagnostic_code(diagnostic.code),
            message: diagnostic.message.clone(),
            source: diagnostic.source.clone(),
            location: diagnostic.location.map(|location| SourceLocation {
                start_line: location.start_line,
                start_column: location.start_column,
                end_line: location.end_line,
                end_column: location.end_column,
            }),
            source_map_key: None,
            input_addresses: diagnostic.input_addresses.clone(),
        }
    }
}

impl ToDiagnostic for FrontendDiagnostic {
    fn to_diagnostic(&self) -> Diagnostic {
        let mut diagnostic = Diagnostic::error(
            self.code.clone(),
            self.message.clone(),
            self.source_map_key
                .clone()
                .map_or(Location::None, Location::Definition),
        );
        diagnostic.severity = self.severity.into();
        if let Some(location) = self.location {
            diagnostic
                .secondary
                .push(Label::new(Location::Generated(DiagnosticGeneratedRange {
                    artifact: self
                        .source
                        .clone()
                        .unwrap_or_else(|| "native-definition".to_owned()),
                    start_line: location.start_line,
                    start_column: location.start_column,
                    end_line: location.end_line,
                    end_column: location.end_column,
                })));
        }
        diagnostic
    }
}

fn native_diagnostic_code(code: NativeDiagnosticCode) -> Code {
    // k-rust treats `DiagnosticCode::as_str` as a compatibility surface, so KRS forwards it unchanged.
    Code::foreign(code.as_str())
}

/// Rejection by the pinned native preparation boundary.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum PreparationError {
    /// The pinned embedded prelude is unavailable.
    MissingPrelude,
    /// The structured loader rejected the definition.
    Loader {
        /// Complete pinned loader error.
        error: Box<k_rust::outer::LoadError>,
        /// Adapted loader diagnostics, with resolved source keys when available.
        diagnostics: Vec<FrontendDiagnostic>,
    },
}

impl PreparationError {
    /// Structured diagnostics produced by preparation.
    #[must_use]
    pub fn diagnostics(&self) -> &[FrontendDiagnostic] {
        match self {
            Self::MissingPrelude => &[],
            Self::Loader { diagnostics, .. } => diagnostics,
        }
    }

    pub(super) fn resolve_diagnostics(&mut self, origins: &[OriginMapping]) {
        if let Self::Loader { diagnostics, .. } = self {
            resolve_diagnostic_keys(origins, diagnostics);
        }
    }
}

impl From<k_rust::outer::LoadError> for PreparationError {
    fn from(error: k_rust::outer::LoadError) -> Self {
        let diagnostics = match &error {
            k_rust::outer::LoadError::SourceDiagnostics(diagnostics) => {
                diagnostics.iter().map(Into::into).collect()
            }
            _ => Vec::new(),
        };
        Self::Loader {
            error: Box::new(error),
            diagnostics,
        }
    }
}

impl fmt::Display for PreparationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingPrelude => {
                formatter.write_str("pinned structured-loader prelude is unavailable")
            }
            Self::Loader { error, diagnostics } => {
                error.fmt(formatter)?;
                display_diagnostics(formatter, diagnostics)
            }
        }
    }
}

impl Error for PreparationError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::MissingPrelude => None,
            Self::Loader { error, .. } => Some(error.as_ref()),
        }
    }
}

/// Permanent structured compilation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DefinitionCompileError {
    /// Definition IR could not be represented by the schema-9 adapter.
    Adapter(AdapterError),
    /// The pinned public preparation primitives rejected the native graph.
    Preparation(PreparationError),
    /// Native input provenance did not join to the adapted Definition IR.
    Provenance(ProvenanceError),
    /// The ordered native compiler rejected the prepared graph.
    Compile(CompileError),
    /// A produced KORE definition did not reparse under the exact pin.
    KoreReparse {
        /// Artifact which failed.
        artifact: &'static str,
        /// Complete pinned parser error, including its byte offset.
        error: k_rust::kore::parser::ParseError,
    },
}

impl DefinitionCompileError {
    /// Structured frontend diagnostics produced by preparation or compilation.
    #[must_use]
    pub fn diagnostics(&self) -> &[FrontendDiagnostic] {
        match self {
            Self::Preparation(error) => error.diagnostics(),
            Self::Compile(error) => error.diagnostics(),
            Self::Adapter(_) | Self::Provenance(_) | Self::KoreReparse { .. } => &[],
        }
    }
}

impl ToDiagnostic for DefinitionCompileError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::Adapter(error) => return error.to_diagnostic(),
            Self::Provenance(error) => return error.to_diagnostic(),
            Self::Preparation(PreparationError::MissingPrelude) => codes::native::MISSING_PRELUDE,
            Self::Preparation(PreparationError::Loader { .. }) => codes::native::PREPARATION,
            Self::Compile(_) => codes::native::COMPILE,
            Self::KoreReparse { .. } => codes::native::KORE_REPARSE,
        };
        Diagnostic::error(code, self.to_string(), Location::None)
    }
}

impl fmt::Display for DefinitionCompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Adapter(error) => error.fmt(formatter),
            Self::Preparation(error) => write!(formatter, "native preparation failed: {error}"),
            Self::Provenance(error) => error.fmt(formatter),
            Self::Compile(error) => error.fmt(formatter),
            Self::KoreReparse { artifact, error } => {
                write!(formatter, "pinned parser rejected {artifact}: {error}")
            }
        }
    }
}

impl Error for DefinitionCompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Adapter(error) => Some(error),
            Self::Preparation(error) => Some(error),
            Self::Provenance(error) => Some(error),
            Self::Compile(error) => Some(error),
            Self::KoreReparse { error, .. } => Some(error),
        }
    }
}

fn display_diagnostics(
    formatter: &mut fmt::Formatter<'_>,
    diagnostics: &[FrontendDiagnostic],
) -> fmt::Result {
    for diagnostic in diagnostics {
        write!(formatter, "\n{}: {}", diagnostic.code, diagnostic.message)?;
    }
    Ok(())
}

pub(super) fn resolve_diagnostic_keys(
    origins: &[OriginMapping],
    diagnostics: &mut [FrontendDiagnostic],
) {
    for diagnostic in diagnostics {
        diagnostic.source_map_key = diagnostic_source_map_key(origins, diagnostic);
    }
}

/// Resolve a native diagnostic's Structured sentence address to its KRS source key.
#[must_use]
pub fn diagnostic_source_map_key(
    origins: &[OriginMapping],
    diagnostic: &FrontendDiagnostic,
) -> Option<SourceMapKey> {
    diagnostic.input_addresses.iter().find_map(|address| {
        (address.input == InputSpace::Structured)
            .then(|| {
                origins.iter().find(|mapping| {
                    mapping.module == address.module
                        && mapping.place
                            == NativeNodePlace::Sentence {
                                index: address.index as usize,
                                role: SentenceNodeRole::Sentence,
                            }
                })
            })
            .flatten()
            .map(|mapping| mapping.key.clone())
    })
}

/// Failure from a named stage of the native frontend pipeline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileError {
    pub(super) diagnostics: Vec<FrontendDiagnostic>,
    source: Box<kompile::CompileError>,
}

impl CompileError {
    /// Name of the frontend stage which failed.
    #[must_use]
    pub const fn stage(&self) -> &'static str {
        self.source.stage
    }

    /// Frontend message associated with the failed stage.
    #[must_use]
    pub fn message(&self) -> &str {
        &self.source.message
    }

    /// Structured diagnostics produced by the failed stage.
    #[must_use]
    pub fn diagnostics(&self) -> &[FrontendDiagnostic] {
        &self.diagnostics
    }
}

impl From<kompile::CompileError> for CompileError {
    fn from(source: kompile::CompileError) -> Self {
        Self {
            diagnostics: source.diagnostics.iter().map(Into::into).collect(),
            source: Box::new(source),
        }
    }
}

impl fmt::Display for CompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        write!(
            formatter,
            "native frontend stage {} failed: {}",
            self.source.stage, self.source.message
        )?;
        display_diagnostics(formatter, &self.diagnostics)
    }
}

impl Error for CompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.source.as_ref())
    }
}

#[cfg(test)]
mod tests;
