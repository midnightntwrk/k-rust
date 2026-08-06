//! Portable, renderer-independent frontend diagnostics.

use crate::definition::{Location, Sentence};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DiagnosticCode {
    DuplicateSentenceLabel,
    InvalidAnonymousVariable,
    InvalidAsPattern,
    InvalidAssociativity,
    InvalidExistentialVariable,
    InvalidFunctionPattern,
    InvalidRewrite,
    MultipleTopSorts,
    InvalidTokenProduction,
    UnusedVariable,
    UnboundVariable,
    UnsupportedExistentialVariable,
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: DiagnosticCode,
    pub message: String,
    pub source: Option<String>,
    pub location: Option<Location>,
}

impl Diagnostic {
    pub fn error(code: DiagnosticCode, message: impl Into<String>, sentence: &Sentence) -> Self {
        Self::new(Severity::Error, code, message, sentence)
    }

    pub fn warning(code: DiagnosticCode, message: impl Into<String>, sentence: &Sentence) -> Self {
        Self::new(Severity::Warning, code, message, sentence)
    }

    fn new(
        severity: Severity,
        code: DiagnosticCode,
        message: impl Into<String>,
        sentence: &Sentence,
    ) -> Self {
        Self {
            severity,
            code,
            message: message.into(),
            source: sentence.attributes().source().map(str::to_owned),
            location: sentence.attributes().location(),
        }
    }
}
