//! Portable, renderer-independent frontend diagnostics.

use crate::definition::{Attributes, Location, Sentence};
use crate::provenance::InputAddress;
use std::fmt;

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum Severity {
    Error,
    Warning,
}

impl Severity {
    /// The severity's stable public identifier: `"error"` or `"warning"`.
    ///
    /// There is intentionally no `Display` implementation: `Debug` prints the
    /// capitalised variant name, and a second, differently cased textual form
    /// behind `{}` would let a formatting change silently alter output.
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Error => "error",
            Self::Warning => "warning",
        }
    }
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

macro_rules! diagnostic_codes {
    ($($variant:ident => $spelling:literal,)*) => {
        /// The kind of a frontend diagnostic.
        ///
        /// Each code has a stable spelling, [`DiagnosticCode::as_str`], that is
        /// written out explicitly beside its variant so that renaming the
        /// variant cannot change it.
        #[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
        pub enum DiagnosticCode {
            $($variant,)*
        }

        impl DiagnosticCode {
            /// Every diagnostic code, in declaration order.
            pub const ALL: &'static [DiagnosticCode] = &[$(Self::$variant,)*];

            /// The code's stable public identifier.
            ///
            /// Renderers, bindings, and downstream tools publish this spelling,
            /// and users search for it and tests assert on it. A variant rename
            /// keeps its spelling, and a retired spelling is never reused for a
            /// different code. It is deliberately independent of the `Debug`
            /// output, which follows the variant name.
            pub const fn as_str(self) -> &'static str {
                match self {
                    $(Self::$variant => $spelling,)*
                }
            }
        }
    };
}

diagnostic_codes! {
    CellCollectionVarWithoutInitial => "CellCollectionVarWithoutInitial",
    ClaimInDefinition => "ClaimInDefinition",
    DeprecatedAttribute => "DeprecatedAttribute",
    DeprecatedProduction => "DeprecatedProduction",
    DuplicateOverload => "DuplicateOverload",
    DuplicateSentenceLabel => "DuplicateSentenceLabel",
    DuplicateConfigurationCell => "DuplicateConfigurationCell",
    DuplicateKLabel => "DuplicateKLabel",
    DuplicateUserList => "DuplicateUserList",
    FutureError => "FutureError",
    InvalidAnonymousVariable => "InvalidAnonymousVariable",
    InvalidAttribute => "InvalidAttribute",
    InvalidAsPattern => "InvalidAsPattern",
    InvalidBracketProduction => "InvalidBracketProduction",
    InvalidAssociativity => "InvalidAssociativity",
    InvalidCommutativeSimplification => "InvalidCommutativeSimplification",
    InvalidConstantFolding => "InvalidConstantFolding",
    InvalidCellConcretization => "InvalidCellConcretization",
    InvalidContext => "InvalidContext",
    InvalidExistentialVariable => "InvalidExistentialVariable",
    InvalidFunctionPattern => "InvalidFunctionPattern",
    InvalidFreshConstant => "InvalidFreshConstant",
    InvalidFunctionConfiguration => "InvalidFunctionConfiguration",
    InvalidLocalFunction => "InvalidLocalFunction",
    InvalidHole => "InvalidHole",
    InvalidHeatCool => "InvalidHeatCool",
    InvalidListDeclaration => "InvalidListDeclaration",
    InvalidMainCell => "InvalidMainCell",
    InvalidMacroExpansion => "InvalidMacroExpansion",
    InvalidOrPattern => "InvalidOrPattern",
    InvalidRegex => "InvalidRegex",
    InvalidRewrite => "InvalidRewrite",
    InvalidIoStream => "InvalidIoStream",
    IsSortPredicateConflict => "IsSortPredicateConflict",
    InvalidSmtLemma => "InvalidSmtLemma",
    InvalidSemanticCast => "InvalidSemanticCast",
    InvalidSimplification => "InvalidSimplification",
    InvalidStreamCell => "InvalidStreamCell",
    InvalidStrictness => "InvalidStrictness",
    InvalidUnitAttribute => "InvalidUnitAttribute",
    IllegalFunctionOnLhs => "IllegalFunctionOnLhs",
    InconsistentFunctionRuleAttributes => "InconsistentFunctionRuleAttributes",
    MultipleTopSorts => "MultipleTopSorts",
    InvalidTokenProduction => "InvalidTokenProduction",
    InvalidDomainValue => "InvalidDomainValue",
    MarkdownWarning => "MarkdownWarning",
    MissingSyntaxModule => "MissingSyntaxModule",
    ProofModuleRule => "ProofModuleRule",
    ProofModuleSyntax => "ProofModuleSyntax",
    SingletonOverload => "SingletonOverload",
    UnusedVariable => "UnusedVariable",
    UnboundVariable => "UnboundVariable",
    UnadmittedHookNamespace => "UnadmittedHookNamespace",
    UnsupportedExistentialVariable => "UnsupportedExistentialVariable",
    UnsupportedCellBag => "UnsupportedCellBag",
    UndefinedKLabel => "UndefinedKLabel",
    UndeclaredTag => "UndeclaredTag",
    UndefinedSort => "UndefinedSort",
    UnrecognizedAttribute => "UnrecognizedAttribute",
    UnsupportedParametricSort => "UnsupportedParametricSort",
    UnusedSymbol => "UnusedSymbol",
}

impl fmt::Display for DiagnosticCode {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.write_str(self.as_str())
    }
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
    fn diagnostic_code_spellings_are_distinct_and_ordered() {
        let mut spellings = std::collections::BTreeSet::new();
        for code in DiagnosticCode::ALL {
            assert!(
                spellings.insert(code.as_str()),
                "{code:?} reuses the spelling {:?}",
                code.as_str()
            );
        }
        // ALL follows declaration order, which is also the derived `Ord`.
        assert!(DiagnosticCode::ALL.windows(2).all(|pair| pair[0] < pair[1]));
    }

    #[test]
    fn diagnostic_code_spellings_are_pinned() {
        assert_eq!(DiagnosticCode::UndefinedKLabel.as_str(), "UndefinedKLabel");
        assert_eq!(DiagnosticCode::UnusedVariable.to_string(), "UnusedVariable");
        assert_eq!(Severity::Error.as_str(), "error");
        assert_eq!(Severity::Warning.as_str(), "warning");
    }

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
