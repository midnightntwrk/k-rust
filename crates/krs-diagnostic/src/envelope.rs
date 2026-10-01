//! Stable diagnostic envelopes shared across process boundaries.

use crate::{Diagnostic, Location, Severity};
use krs_ir::{SourceMapKey, SourceRange};
use serde::{Deserialize, Serialize};

/// Version of the stable diagnostic JSON envelope.
pub const DIAGNOSTIC_SCHEMA_VERSION: u32 = 1;

/// Compiler boundary which produced a diagnostic.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "kebab-case")]
pub enum DiagnosticStage {
    /// rustc or proc-macro expansion of ordinary authored Rust.
    RustExpansion,
    /// Cross-item KRS collection, analysis, or Definition-IR lowering.
    Analysis,
    /// Parsing or checking canonical generated K source.
    KFrontend,
    /// Native frontend adaptation or definition checks.
    Native,
}

/// Severity independent of rustc, K, or `k-rust` renderer types.
#[derive(Clone, Copy, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(rename_all = "lowercase")]
pub enum DiagnosticSeverity {
    /// Compilation cannot continue.
    Error,
    /// Compilation can continue, but the author should inspect the issue.
    Warning,
}

/// An honest location in a generated artifact or downstream frontend.
///
/// Lines and columns are one-based and inclusive at the start.
/// The end is the downstream tool's exact reported end; KRS does not reinterpret or invent missing coordinates.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DiagnosticGeneratedRange {
    /// Stable artifact/source identifier, never a temporary checkout path.
    pub artifact: String,
    /// One-based starting line.
    pub start_line: u32,
    /// One-based starting column.
    pub start_column: u32,
    /// One-based ending line.
    pub end_line: u32,
    /// One-based ending column.
    pub end_column: u32,
}

/// One stable machine-readable diagnostic shared by all KRS commands.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DiagnosticEnvelope {
    /// Wire schema for fail-closed consumers.
    pub schema_version: u32,
    /// Compiler boundary which produced the diagnostic.
    pub stage: DiagnosticStage,
    /// Stable KRS code or stable-within-a-pin upstream code.
    pub code: String,
    /// Renderer-independent severity.
    pub severity: DiagnosticSeverity,
    /// Human-readable detail; consumers must classify by `code`.
    pub message: String,
    /// Exact parser-owned authored byte range.
    pub authored_range: SourceRange,
    /// Exact downstream range when one was actually reported.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generated_range: Option<DiagnosticGeneratedRange>,
    /// Stable supplemental detail, in deterministic order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub notes: Vec<String>,
}

impl DiagnosticEnvelope {
    /// Constructs an error anchored to exact authored tokens.
    #[must_use]
    pub fn error(
        stage: DiagnosticStage,
        code: impl Into<String>,
        message: impl Into<String>,
        authored_range: SourceRange,
    ) -> Self {
        Self {
            schema_version: DIAGNOSTIC_SCHEMA_VERSION,
            stage,
            code: code.into(),
            severity: DiagnosticSeverity::Error,
            message: message.into(),
            authored_range,
            generated_range: None,
            notes: Vec::new(),
        }
    }

    /// Decodes diagnostic JSON lines and rejects unsupported schemas.
    ///
    /// # Errors
    ///
    /// Returns an error for malformed envelopes, unknown fields, or unsupported schema versions.
    pub fn from_json_lines(text: &str) -> serde_json::Result<Vec<Self>> {
        text.lines()
            .map(|line| {
                let envelope: Self = serde_json::from_str(line)?;
                if envelope.schema_version != DIAGNOSTIC_SCHEMA_VERSION {
                    return Err(<serde_json::Error as serde::de::Error>::custom(format!(
                        "unsupported diagnostic schema version {}",
                        envelope.schema_version
                    )));
                }
                Ok(envelope)
            })
            .collect()
    }

    /// Serialize one canonical JSON line for CLI and editor consumers.
    ///
    /// # Errors
    ///
    /// Returns a JSON error if the stable envelope cannot be encoded.
    pub fn to_json_line(&self) -> serde_json::Result<String> {
        let mut value = serde_json::to_string(self)?;
        value.push('\n');
        Ok(value)
    }
}

/// Builds the envelope view of a diagnostic with an exact authored range.
/// Definition locations require exact source-map resolution from the producing boundary.
/// Diagnostics without one exact authored range remain available to prose renderers.
#[must_use]
pub fn diagnostic_envelope(
    diagnostic: Diagnostic,
    stage: DiagnosticStage,
    resolve: impl FnOnce(&SourceMapKey) -> Option<SourceRange>,
) -> Option<DiagnosticEnvelope> {
    let generated_range = std::iter::once(&diagnostic.primary)
        .chain(&diagnostic.secondary)
        .find_map(|label| match &label.location {
            Location::Generated(range) => Some(range.clone()),
            _ => None,
        });
    let authored_range = match diagnostic.primary.location {
        Location::Source(range) => range,
        Location::Definition(key) => resolve(&key)?,
        _ => return None,
    };
    Some(DiagnosticEnvelope {
        schema_version: DIAGNOSTIC_SCHEMA_VERSION,
        stage,
        code: diagnostic.code.to_string(),
        severity: match diagnostic.severity {
            Severity::Error => DiagnosticSeverity::Error,
            Severity::Warning => DiagnosticSeverity::Warning,
        },
        message: diagnostic.message,
        authored_range,
        generated_range,
        notes: diagnostic.notes,
    })
}
