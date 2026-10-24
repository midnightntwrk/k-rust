//! Stable diagnostic envelopes shared across process boundaries.

use crate::codes::{self, CodeKind};
use crate::{Diagnostic, Location, Severity};
use krs_ir::{SourceMapKey, SourceRange};
use serde::{Deserialize, Serialize};

/// Version of the stable diagnostic JSON envelope.
pub const DIAGNOSTIC_SCHEMA_VERSION: u32 = 2;

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

impl From<Severity> for DiagnosticSeverity {
    fn from(severity: Severity) -> Self {
        match severity {
            Severity::Error => Self::Error,
            Severity::Warning => Self::Warning,
        }
    }
}

impl From<DiagnosticSeverity> for Severity {
    fn from(severity: DiagnosticSeverity) -> Self {
        match severity {
            DiagnosticSeverity::Error => Self::Error,
            DiagnosticSeverity::Warning => Self::Warning,
        }
    }
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

/// A related authored location of a diagnostic.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DiagnosticLabel {
    /// Exact parser-owned authored byte range.
    pub range: SourceRange,
    /// What this location contributes, written for display beside it.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub message: Option<String>,
}

/// One stable machine-readable diagnostic shared by all KRS commands.
///
/// Every diagnostic is an envelope. One without an authored range has no authored text as its
/// subject: an absence, the environment, generated K no authored node produced, or the command
/// line; `item` names its subject item when that item has no exact range of its own.
#[derive(Clone, Debug, Eq, PartialEq, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DiagnosticEnvelope {
    /// Wire schema for fail-closed consumers.
    pub schema_version: u32,
    /// Compiler boundary which produced the diagnostic.
    pub stage: DiagnosticStage,
    /// Stable KRS code or stable-within-a-pin upstream code.
    pub code: String,
    /// Who can act on the condition: the registry's kind for a KRS code, `author` for a forwarded
    /// one, which judges authored text.
    pub kind: CodeKind,
    /// Renderer-independent severity.
    pub severity: DiagnosticSeverity,
    /// Human-readable detail; consumers must classify by `code`.
    pub message: String,
    /// Exact parser-owned authored byte range, `null` when no authored text is the subject.
    pub authored_range: Option<SourceRange>,
    /// The stable identity of the subject item when it has no exact range.
    #[serde(default, skip_serializing_if = "Option::is_none")]
    pub item: Option<String>,
    /// Exact downstream range when one was actually reported.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub generated_range: Option<DiagnosticGeneratedRange>,
    /// Related authored locations, in producer order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub labels: Vec<DiagnosticLabel>,
    /// Stable supplemental detail, in deterministic order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub notes: Vec<String>,
    /// Advice on how to fix the problem, in deterministic order.
    #[serde(default, skip_serializing_if = "Vec::is_empty")]
    pub help: Vec<String>,
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
        Self::unlocated(stage, code, message).at(authored_range)
    }

    /// Constructs an error that no authored text is the subject of.
    #[must_use]
    pub fn unlocated(
        stage: DiagnosticStage,
        code: impl Into<String>,
        message: impl Into<String>,
    ) -> Self {
        let code = code.into();
        Self {
            schema_version: DIAGNOSTIC_SCHEMA_VERSION,
            stage,
            kind: kind_of(&code),
            code,
            severity: DiagnosticSeverity::Error,
            message: message.into(),
            authored_range: None,
            item: None,
            generated_range: None,
            labels: Vec::new(),
            notes: Vec::new(),
            help: Vec::new(),
        }
    }

    /// This diagnostic located at `authored_range`.
    #[must_use]
    pub fn at(mut self, authored_range: SourceRange) -> Self {
        self.authored_range = Some(authored_range);
        self
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

/// The envelope kind of a code: the registry's kind for a KRS code, and `author` for a code
/// forwarded from rustc or a native frontend, which judges authored text.
#[must_use]
pub fn kind_of(code: &str) -> CodeKind {
    codes::info(code).map_or(CodeKind::Author, |info| info.kind)
}

/// Builds the envelope view of a diagnostic.
///
/// Definition locations require exact source-map resolution from the producing boundary. Only
/// exact authored locations become the envelope's range or its labels: a primary without one
/// gives an envelope with no authored range, and a secondary without one is no label (a
/// generated location still feeds `generated_range`). KRS never invents an authored location.
#[must_use]
pub fn diagnostic_envelope(
    diagnostic: Diagnostic,
    stage: DiagnosticStage,
    resolve: impl Fn(&SourceMapKey) -> Option<SourceRange>,
) -> DiagnosticEnvelope {
    let generated_range = std::iter::once(&diagnostic.primary)
        .chain(&diagnostic.secondary)
        .find_map(|label| match &label.location {
            Location::Generated(range) => Some(range.clone()),
            _ => None,
        });
    let exact = |location: &Location| match location {
        Location::Source(range) => Some(range.clone()),
        Location::Definition(key) => resolve(key),
        _ => None,
    };
    let authored_range = exact(&diagnostic.primary.location);
    let labels = diagnostic
        .secondary
        .iter()
        .filter_map(|label| {
            Some(DiagnosticLabel {
                range: exact(&label.location)?,
                message: label.message.clone(),
            })
        })
        .collect();
    DiagnosticEnvelope {
        schema_version: DIAGNOSTIC_SCHEMA_VERSION,
        stage,
        kind: kind_of(diagnostic.code.as_str()),
        code: diagnostic.code.to_string(),
        severity: diagnostic.severity.into(),
        message: diagnostic.message,
        authored_range,
        item: diagnostic.item,
        generated_range,
        labels,
        notes: diagnostic.notes,
        help: diagnostic.help,
    }
}
