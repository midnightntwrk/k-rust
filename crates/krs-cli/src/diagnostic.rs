//! Renderer-independent diagnostics for every production KRS boundary.

use krs_compiler::SourceMap;
use krs_ir::{OriginFrame, RangedOriginKind, SourceMapKey, SourceRange};
use krs_k_rust::{DiagnosticSeverity as NativeSeverity, FrontendDiagnostic};
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
/// Lines and columns are one-based and inclusive at the start. The end is the
/// downstream tool's exact reported end; KRS does not reinterpret or invent
/// missing coordinates.
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
    /// Construct an error anchored to exact authored tokens.
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

/// Return the exact authored range for one Definition source-map key.
///
/// This function fails closed: absent keys, absent authored frames, and
/// multiple authored frames are not guessed or replaced with a sentence
/// range.
#[must_use]
pub fn exact_authored_range(source_map: &SourceMap, key: &SourceMapKey) -> Option<SourceRange> {
    let entry = source_map
        .entries()
        .iter()
        .find(|entry| entry.key() == key)?;
    exact_authored_range_from_origin(entry.origin())
}

/// Return the sole exact authored range in an origin stack.
///
/// Multiple authored frames are rejected rather than resolved by proximity.
#[must_use]
pub fn exact_authored_range_from_origin(origin: &krs_ir::OriginStack) -> Option<SourceRange> {
    let mut authored = origin.frames().iter().filter_map(|frame| match frame {
        OriginFrame::Ranged {
            kind: RangedOriginKind::Authored,
            range,
            ..
        } => Some(range),
        _ => None,
    });
    let range = authored.next()?.clone();
    if authored.next().is_some() {
        return None;
    }
    Some(range)
}

/// Translate a native diagnostic through an exact Definition source-map key.
///
/// A native location is retained only when the frontend supplied all four
/// coordinates. The authored range always comes from the parser-owned origin
/// stack rather than from the generated location.
#[must_use]
pub fn translate_native_diagnostic(
    source_map: &SourceMap,
    key: &SourceMapKey,
    diagnostic: &FrontendDiagnostic,
) -> Option<DiagnosticEnvelope> {
    let authored_range = exact_authored_range(source_map, key)?;
    let generated_range = diagnostic
        .location
        .map(|location| DiagnosticGeneratedRange {
            artifact: diagnostic
                .source
                .clone()
                .unwrap_or_else(|| "native-definition".to_owned()),
            start_line: location.start_line,
            start_column: location.start_column,
            end_line: location.end_line,
            end_column: location.end_column,
        });
    Some(DiagnosticEnvelope {
        schema_version: DIAGNOSTIC_SCHEMA_VERSION,
        stage: DiagnosticStage::Native,
        code: diagnostic.code.clone(),
        severity: match diagnostic.severity {
            NativeSeverity::Error => DiagnosticSeverity::Error,
            NativeSeverity::Warning => DiagnosticSeverity::Warning,
        },
        message: diagnostic.message.clone(),
        authored_range,
        generated_range,
        notes: Vec::new(),
    })
}

/// Translate a generated-K frontend range through a unique `sources.json`
/// entry selected by its generated byte interval.
///
/// The frontend's line/column location is retained for display. Selection is
/// performed with exact generated byte offsets because line/column-only
/// containment is ambiguous and must never be used to guess an authored
/// token.
#[must_use]
pub fn translate_k_frontend_diagnostic(
    source_map: &SourceMap,
    code: impl Into<String>,
    message: impl Into<String>,
    generated_start_byte: u64,
    generated_end_byte: u64,
    generated_range: DiagnosticGeneratedRange,
) -> Option<DiagnosticEnvelope> {
    let mut matches = source_map.entries().iter().filter(|entry| {
        entry.generated().is_some_and(|range| {
            range.artifact() == generated_range.artifact
                && range.start_byte() == generated_start_byte
                && range.end_byte() == generated_end_byte
        })
    });
    let entry = matches.next()?;
    if matches.next().is_some() {
        return None;
    }
    let authored_range = exact_authored_range(source_map, entry.key())?;
    Some(DiagnosticEnvelope {
        schema_version: DIAGNOSTIC_SCHEMA_VERSION,
        stage: DiagnosticStage::KFrontend,
        code: code.into(),
        severity: DiagnosticSeverity::Error,
        message: message.into(),
        authored_range,
        generated_range: Some(generated_range),
        notes: Vec::new(),
    })
}

#[cfg(test)]
mod tests {
    use super::*;
    use krs_ir::{OriginStack, PackageId, Sha256Digest, SourceFileId};

    fn range() -> SourceRange {
        let package = PackageId::new("diag", "diag", "0.1.0", "workspace").unwrap();
        let file = SourceFileId::new(
            package,
            "src/lib.rs",
            Sha256Digest::new("11".repeat(32)).unwrap(),
        )
        .unwrap();
        SourceRange::new(file, 7, 16).unwrap()
    }

    #[test]
    fn envelope_is_one_canonical_json_line() {
        let envelope = DiagnosticEnvelope::error(
            DiagnosticStage::Analysis,
            "symbol-name-collision",
            "collision",
            range(),
        );
        let json = envelope.to_json_line().unwrap();
        assert!(json.ends_with('\n'));
        assert_eq!(json.lines().count(), 1);
        assert_eq!(
            serde_json::from_str::<DiagnosticEnvelope>(json.trim()).unwrap(),
            envelope
        );
    }

    #[test]
    fn exact_mapping_never_fabricates_a_native_range() {
        let key = SourceMapKey::new("diag.module").unwrap();
        let origin = OriginStack::authored(range());
        let source_map = serde_json::from_value::<SourceMap>(serde_json::json!({
            "schema_version": 2,
            "entries": [{
                "key": key.as_str(),
                "node_kind": "module",
                "origin": origin,
            }],
        }))
        .unwrap();
        assert_eq!(exact_authored_range(&source_map, &key), Some(range()));

        let diagnostic = FrontendDiagnostic {
            severity: NativeSeverity::Error,
            code: "UnsupportedThing".to_owned(),
            message: "unsupported".to_owned(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        };
        let translated = translate_native_diagnostic(&source_map, &key, &diagnostic)
            .expect("exact authored mapping");
        assert_eq!(translated.authored_range, range());
        assert_eq!(translated.generated_range, None);
    }
}
