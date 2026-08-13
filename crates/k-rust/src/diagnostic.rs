//! Portable, renderer-independent frontend diagnostics.

use crate::definition::{Attributes, Location, Sentence};

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Severity {
    Error,
    Warning,
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DiagnosticCode {
    DeprecatedAttribute,
    DuplicateSentenceLabel,
    DuplicateConfigurationCell,
    DuplicateKLabel,
    InvalidAnonymousVariable,
    InvalidAttribute,
    InvalidAsPattern,
    InvalidBracketProduction,
    InvalidAssociativity,
    InvalidCommutativeSimplification,
    InvalidConstantFolding,
    InvalidContext,
    InvalidExistentialVariable,
    InvalidFunctionPattern,
    InvalidFunctionConfiguration,
    InvalidLocalFunction,
    InvalidHole,
    InvalidHeatCool,
    InvalidListDeclaration,
    InvalidRegex,
    InvalidRewrite,
    InvalidIoStream,
    InvalidSmtLemma,
    InvalidSemanticCast,
    InvalidStreamCell,
    InvalidStrictness,
    IllegalFunctionOnLhs,
    InconsistentFunctionRuleAttributes,
    MultipleTopSorts,
    InvalidTokenProduction,
    UnusedVariable,
    UnboundVariable,
    UnsupportedExistentialVariable,
    UnsupportedCellBag,
    UndefinedKLabel,
    UnrecognizedAttribute,
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

    pub fn error_at(
        code: DiagnosticCode,
        message: impl Into<String>,
        attributes: &Attributes,
    ) -> Self {
        Self::at(Severity::Error, code, message, attributes)
    }

    pub fn warning_at(
        code: DiagnosticCode,
        message: impl Into<String>,
        attributes: &Attributes,
    ) -> Self {
        Self::at(Severity::Warning, code, message, attributes)
    }

    pub fn error_at_location(
        code: DiagnosticCode,
        message: impl Into<String>,
        source: impl Into<String>,
        location: Location,
    ) -> Self {
        Self {
            severity: Severity::Error,
            code,
            message: message.into(),
            source: Some(source.into()),
            location: Some(location),
        }
    }

    fn new(
        severity: Severity,
        code: DiagnosticCode,
        message: impl Into<String>,
        sentence: &Sentence,
    ) -> Self {
        Self::at(severity, code, message, sentence.attributes())
    }

    fn at(
        severity: Severity,
        code: DiagnosticCode,
        message: impl Into<String>,
        attributes: &Attributes,
    ) -> Self {
        Self {
            severity,
            code,
            message: message.into(),
            source: attributes.source().map(str::to_owned),
            location: attributes.location(),
        }
    }
}
