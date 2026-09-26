//! Portable, renderer-independent frontend diagnostics.

use crate::definition::{Attributes, Location, Sentence};
use crate::provenance::InputAddress;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Severity {
    Error,
    Warning,
}

/// Warning categories in the order used by K's `ExceptionType`.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum WarningCategory {
    NonExhaustiveMatch,
    UndeletedTempDir,
    MissingSyntaxModule,
    InvalidExitCode,
    InvalidConfigVar,
    InvalidAssociativity,
    FutureError,
    UnusedVar,
    ProofLint,
    NonLrGrammar,
    IgnoredAttribute,
    RemovedAnywhere,
    DeprecatedSymbol,
    MissingHook,
    SingletonOverload,
    DuplicateOverload,
    CellCollectionVarWithoutInitial,
    UselessRule,
    UnresolvedFunctionSymbol,
    MalformedMarkdown,
    InvalidatedCache,
    UnusedSymbol,
}

impl WarningCategory {
    fn hidden(self) -> bool {
        self >= Self::UselessRule
    }
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum WarningLevel {
    All,
    #[default]
    Normal,
    None,
}

#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub struct DiagnosticPolicy {
    pub level: WarningLevel,
    pub warnings_to_errors: bool,
}

impl DiagnosticPolicy {
    pub fn includes(self, category: WarningCategory) -> bool {
        match self.level {
            WarningLevel::All => true,
            WarningLevel::Normal => !category.hidden(),
            WarningLevel::None => false,
        }
    }

    /// Drop excluded warnings and upgrade included warnings when requested.
    pub fn apply(self, diagnostics: Vec<Diagnostic>) -> Vec<Diagnostic> {
        diagnostics
            .into_iter()
            .filter_map(|mut diagnostic| {
                if diagnostic.severity == Severity::Error {
                    return Some(diagnostic);
                }
                let included = diagnostic
                    .code
                    .warning_category()
                    .map_or(self.level != WarningLevel::None, |category| {
                        self.includes(category)
                    });
                if !included {
                    return None;
                }
                if self.warnings_to_errors {
                    diagnostic.severity = Severity::Error;
                }
                Some(diagnostic)
            })
            .collect()
    }
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum DiagnosticCode {
    CellCollectionVarWithoutInitial,
    ClaimInDefinition,
    DeprecatedAttribute,
    DeprecatedProduction,
    DuplicateOverload,
    DuplicateSentenceLabel,
    DuplicateConfigurationCell,
    DuplicateKLabel,
    DuplicateUserList,
    FutureError,
    InvalidAnonymousVariable,
    InvalidAttribute,
    InvalidAsPattern,
    InvalidBracketProduction,
    InvalidAssociativity,
    InvalidCommutativeSimplification,
    InvalidConstantFolding,
    InvalidCellConcretization,
    InvalidContext,
    InvalidExistentialVariable,
    InvalidFunctionPattern,
    InvalidFreshConstant,
    InvalidFunctionConfiguration,
    InvalidLocalFunction,
    InvalidHole,
    InvalidHeatCool,
    InvalidListDeclaration,
    InvalidMainCell,
    InvalidMacroExpansion,
    InvalidOrPattern,
    InvalidRegex,
    InvalidRewrite,
    InvalidIoStream,
    IsSortPredicateConflict,
    InvalidSmtLemma,
    InvalidSemanticCast,
    InvalidSimplification,
    InvalidStreamCell,
    InvalidStrictness,
    InvalidUnitAttribute,
    IllegalFunctionOnLhs,
    InconsistentFunctionRuleAttributes,
    MultipleTopSorts,
    InvalidTokenProduction,
    InvalidDomainValue,
    MarkdownWarning,
    MissingSyntaxModule,
    ProofModuleRule,
    ProofModuleSyntax,
    SingletonOverload,
    UnusedVariable,
    UnboundVariable,
    UnadmittedHookNamespace,
    UnsupportedExistentialVariable,
    UnsupportedCellBag,
    UndefinedKLabel,
    UndeclaredTag,
    UndefinedSort,
    UnrecognizedAttribute,
    UnsupportedParametricSort,
    UnusedSymbol,
}

impl DiagnosticCode {
    pub fn warning_category(self) -> Option<WarningCategory> {
        match self {
            Self::CellCollectionVarWithoutInitial => {
                Some(WarningCategory::CellCollectionVarWithoutInitial)
            }
            Self::DeprecatedAttribute => Some(WarningCategory::FutureError),
            Self::DeprecatedProduction => Some(WarningCategory::DeprecatedSymbol),
            Self::DuplicateOverload => Some(WarningCategory::DuplicateOverload),
            Self::FutureError => Some(WarningCategory::FutureError),
            Self::InvalidAssociativity => Some(WarningCategory::InvalidAssociativity),
            Self::MarkdownWarning => Some(WarningCategory::MalformedMarkdown),
            Self::MissingSyntaxModule => Some(WarningCategory::MissingSyntaxModule),
            Self::SingletonOverload => Some(WarningCategory::SingletonOverload),
            Self::UnadmittedHookNamespace => Some(WarningCategory::MissingHook),
            Self::UnusedVariable => Some(WarningCategory::UnusedVar),
            Self::UnusedSymbol => Some(WarningCategory::UnusedSymbol),
            _ => None,
        }
    }
}

#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct Diagnostic {
    pub severity: Severity,
    pub code: DiagnosticCode,
    pub message: String,
    pub source: Option<String>,
    pub location: Option<Location>,
    pub input_addresses: Vec<InputAddress>,
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
            input_addresses: Vec::new(),
        }
    }

    pub fn warning_at_location(
        code: DiagnosticCode,
        message: impl Into<String>,
        source: impl Into<String>,
        location: Location,
    ) -> Self {
        Self {
            severity: Severity::Warning,
            code,
            message: message.into(),
            source: Some(source.into()),
            location: Some(location),
            input_addresses: Vec::new(),
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
            input_addresses: attributes.input_addresses().to_vec(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::provenance::InputSpace;

    #[test]
    fn attribute_diagnostics_copy_input_addresses() {
        let addresses = vec![InputAddress::new(InputSpace::Structured, "MAIN", 2)];
        let mut attributes = Attributes::default();
        attributes.set_input_addresses(addresses.clone());
        for diagnostic in [
            Diagnostic::error_at(DiagnosticCode::InvalidAttribute, "bad", &attributes),
            Diagnostic::warning_at(DiagnosticCode::InvalidAttribute, "bad", &attributes),
        ] {
            assert_eq!(diagnostic.input_addresses, addresses);
        }
    }

    #[test]
    fn location_only_diagnostics_have_no_input_address() {
        let location = Location {
            start_line: 1,
            start_column: 2,
            end_line: 1,
            end_column: 3,
        };
        for diagnostic in [
            Diagnostic::error_at_location(DiagnosticCode::InvalidAttribute, "bad", "a.k", location),
            Diagnostic::warning_at_location(
                DiagnosticCode::InvalidAttribute,
                "bad",
                "a.k",
                location,
            ),
        ] {
            assert!(diagnostic.input_addresses.is_empty());
        }
    }

    fn diagnostic(severity: Severity, code: DiagnosticCode) -> Diagnostic {
        Diagnostic {
            severity,
            code,
            message: "message".into(),
            source: None,
            location: None,
            input_addresses: Vec::new(),
        }
    }

    #[test]
    fn policy_levels_match_global_options_warnings() {
        let normal = DiagnosticPolicy::default();
        assert!(normal.includes(WarningCategory::UnusedVar));
        assert!(!normal.includes(WarningCategory::MalformedMarkdown));
        assert!(!normal.includes(WarningCategory::UnusedSymbol));

        let all = DiagnosticPolicy {
            level: WarningLevel::All,
            warnings_to_errors: false,
        };
        assert!(all.includes(WarningCategory::MalformedMarkdown));
        assert!(all.includes(WarningCategory::UnusedSymbol));

        let none = DiagnosticPolicy {
            level: WarningLevel::None,
            warnings_to_errors: false,
        };
        assert!(!none.includes(WarningCategory::UnusedVar));
        assert!(!none.includes(WarningCategory::MalformedMarkdown));

        let diagnostics = vec![
            diagnostic(Severity::Warning, DiagnosticCode::UnusedVariable),
            diagnostic(Severity::Warning, DiagnosticCode::MarkdownWarning),
            diagnostic(Severity::Error, DiagnosticCode::InvalidAttribute),
        ];
        assert_eq!(
            none.apply(diagnostics.clone()),
            vec![diagnostics[2].clone()]
        );

        let upgraded = DiagnosticPolicy {
            level: WarningLevel::Normal,
            warnings_to_errors: true,
        }
        .apply(diagnostics);
        assert_eq!(upgraded.len(), 2);
        assert_eq!(upgraded[0].code, DiagnosticCode::UnusedVariable);
        assert_eq!(upgraded[0].severity, Severity::Error);
        assert_eq!(upgraded[1].code, DiagnosticCode::InvalidAttribute);
        assert_eq!(upgraded[1].severity, Severity::Error);
    }
}
