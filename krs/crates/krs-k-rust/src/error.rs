use std::{error::Error, fmt};

use k_rust::{
    diagnostic::{
        Diagnostic as NativeDiagnostic, DiagnosticCode as NativeDiagnosticCode,
        Severity as NativeSeverity,
    },
    kompile,
};
use krs_diagnostic::{
    Code, Diagnostic, Label, Location, Severity, ToDiagnostic,
    codes::{self, CodeKind},
    envelope::DiagnosticGeneratedRange,
};
use krs_ir::SourceMapKey;

use crate::{
    InputAddress, InputSpace,
    adapter::{AdapterError, NativeNodePlace, OriginMapping, SentenceNodeRole, SentenceProducer},
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
    /// Stable-within-the-pin native diagnostic code name, with its kind: its kind on lowered K
    /// until the adapter finds the sentence it names (`attribute_diagnostics`).
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
    /// Advice in KRS's terms, where the native frontend's message gives advice KRS's command line
    /// cannot follow.
    pub help: Vec<String>,
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
            help: native_help(diagnostic.code)
                .into_iter()
                .map(str::to_owned)
                .collect(),
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
        diagnostic.help.clone_from(&self.help);
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
    Code::foreign(code.as_str(), native_kind(code))
}

/// Who can act on a native diagnostic about a sentence KRS lowered, or about no KRS sentence.
///
/// KRS lowers only programs it accepts, into K it means the native frontend to accept. A native
/// refusal of lowered K is therefore the author's only where it judges a property of the author's
/// program that KRS leaves to the native frontend; where KRS checks the same rule earlier under
/// its own code, or produces the construct itself, the refusal is a KRS bug. A code whose meaning
/// is unclear is internal: a wrong internal produces a report, a wrong author hides a bug. The
/// match has no wildcard, so a new native code is classified where it is added.
/// [`attribute_diagnostics`] makes every non-environment code author at a `raw_k!` sentence.
const fn native_kind(code: NativeDiagnosticCode) -> CodeKind {
    use NativeDiagnosticCode as C;
    match code {
        // Properties of the author's program that KRS delegates: a function or projection in a
        // pattern, a hook the selected backend does not implement, a collection cell started
        // present by a configuration variable, an unused binder or constructor, and the value
        // claims' verdicts on the author's equations.
        C::IllegalFunctionOnLhs
        | C::UnadmittedHookNamespace
        | C::CellCollectionVarWithoutInitial
        | C::UnusedVariable
        | C::UnusedSymbol
        | C::UnjoinedCriticalPair
        | C::ValueClaimPrecondition => CodeKind::Author,
        // Whether it fires depends on the calling thread's stack, not on the program.
        C::TermTooDeep => CodeKind::Environment,
        // KRS checks the same rule earlier under its own code: patterns, binders and variables,
        // placement and evaluation, strictness and holes, SMT lemmas and stream cells, spec
        // modules, lists, tokens and sorts, overloads and precedence, and the route's capability.
        C::InvalidAsPattern
        | C::InvalidOrPattern
        | C::InvalidFunctionPattern
        | C::InvalidFunctionConfiguration
        | C::InvalidLocalFunction
        | C::InvalidExistentialVariable
        | C::InvalidFreshConstant
        | C::UnboundVariable
        | C::InvalidBinder
        | C::MlConstructPosition
        | C::InvalidContext
        | C::InvalidHeatCool
        | C::InvalidStrictness
        | C::InvalidHole
        | C::InvalidSmtLemma
        | C::InvalidIoStream
        | C::InvalidStreamCell
        | C::InvalidMainCell
        | C::ProofModuleRule
        | C::ProofModuleSyntax
        | C::DuplicateUserList
        | C::InvalidListDeclaration
        | C::InvalidRegex
        | C::InvalidTokenProduction
        | C::InvalidDomainValue
        | C::UnsupportedParametricSort
        | C::IsSortPredicateConflict
        | C::DuplicateOverload
        | C::SingletonOverload
        | C::InvalidAssociativity
        | C::UnsupportedExistentialVariable
        // KRS produces the construct itself: labels and names, attributes, generated
        // productions, cells and sorts, references, modules and imports, the production a builtin
        // lowers to, substituted constants, simplifications, casts and search patterns, the one
        // rewrite of every rule form, and line markers (none).
        | C::DuplicateKLabel
        | C::DuplicateSentenceLabel
        | C::InvalidAnonymousVariable
        | C::InvalidNumeralSort
        | C::InvalidAttribute
        | C::UnrecognizedAttribute
        | C::DeprecatedAttribute
        | C::InconsistentFunctionRuleAttributes
        | C::InvalidBracketProduction
        | C::InvalidUnitAttribute
        | C::DuplicateConfigurationCell
        | C::UnsupportedCellBag
        | C::InvalidCellConcretization
        | C::MultipleTopSorts
        | C::KernelSortPosition
        | C::InvalidSortSynonym
        | C::UndefinedKLabel
        | C::UndefinedSort
        | C::MissingLocationsImport
        | C::ClaimInDefinition
        | C::DeprecatedProduction
        | C::InvalidConstantFolding
        | C::InvalidCommutativeSimplification
        | C::InvalidSimplification
        | C::InvalidMacroExpansion
        | C::InvalidSemanticCast
        | C::InvalidSearchPattern
        | C::InvalidRewrite
        | C::UnsupportedLineMarker
        // The structured route KRS loads by never raises these: it resolves no syntax module and
        // loads no source text but the embedded prelude's, and the adapter re-codes the parse of
        // a `raw_k!` text (`krs::native::raw-k-parse`).
        | C::MissingSyntaxModule
        | C::FutureError
        | C::MarkdownWarning
        | C::UndeclaredTag => CodeKind::Internal,
    }
}

/// Advice in KRS's terms for a native diagnostic whose own advice names a k-rust option.
const fn native_help(code: NativeDiagnosticCode) -> Option<&'static str> {
    match code {
        // KRS passes no hook namespaces of its own: the backend the author selects admits the
        // plugin namespaces it implements.
        NativeDiagnosticCode::UnadmittedHookNamespace => Some(
            "KRS has no `--hook-namespaces`: `--backend llvm` admits no plugin hook namespace, and `--backend haskell` admits those its backend implements",
        ),
        _ => None,
    }
}

impl FrontendDiagnostic {
    /// The configuration cell a native `CellCollectionVarWithoutInitial` warning names, by its K
    /// name. k-rust attaches no sentence to it, so its message is the only place the cell is
    /// named: "... collection cell <NAME>. ...".
    #[must_use]
    pub fn collection_cell_without_initial(&self) -> Option<&str> {
        if self.code.as_str() != NativeDiagnosticCode::CellCollectionVarWithoutInitial.as_str() {
            return None;
        }
        let (_, rest) = self.message.split_once("collection cell <")?;
        rest.split_once('>').map(|(name, _)| name)
    }
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
            attribute_diagnostics(origins, diagnostics);
        }
    }

    /// Reports a K parse error in a `raw_k!` sentence at the `raw_k!` text
    /// (`krs::native::raw-k-parse`): k-rust names the sentence only by the
    /// source name the adapter gave it.
    pub(super) fn resolve_raw_parse_error(&mut self, ir: &krs_ir_levels::DefinitionIr) {
        let Self::Loader { error, diagnostics } = self else {
            return;
        };
        let k_rust::outer::LoadError::RuleParsing(k_rust::inner::RuleError::Parse(parse)) =
            error.as_ref()
        else {
            return;
        };
        let Some(source) = &parse.source else {
            return;
        };
        let raw = ir
            .modules()
            .iter()
            .flat_map(krs_ir_levels::DefinitionModule::sentences)
            .find_map(|sentence| match sentence {
                krs_ir_levels::DefinitionSentence::Raw(raw)
                    if &crate::adapter::raw_source_name(raw) == source =>
                {
                    Some(raw)
                }
                _ => None,
            });
        if let Some(raw) = raw {
            diagnostics.push(FrontendDiagnostic {
                severity: DiagnosticSeverity::Error,
                code: krs_diagnostic::codes::native::RAW_K_PARSE,
                message: format!(
                    "K cannot parse this `raw_k!` {} with the grammar of module {:?}: {}",
                    raw.kind.keyword(),
                    parse.module,
                    parse.error
                ),
                source: Some(source.clone()),
                location: parse.location.map(|location| SourceLocation {
                    start_line: location.start_line,
                    start_column: location.start_column,
                    end_line: location.end_line,
                    end_column: location.end_column,
                }),
                source_map_key: Some(raw.origin.key().clone()),
                input_addresses: Vec::new(),
                help: Vec::new(),
            });
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

/// Attributes each native diagnostic to the KRS sentence it names: its source-map key, and its
/// kind by who wrote that sentence. Every native refusal of the author's verbatim `raw_k!` text is
/// the author's, except a host limit; a diagnostic about a lowered sentence, the prelude or no
/// sentence keeps its kind on lowered K ([`native_kind`]).
pub(super) fn attribute_diagnostics(
    origins: &[OriginMapping],
    diagnostics: &mut [FrontendDiagnostic],
) {
    for diagnostic in diagnostics {
        let mapping = sentence_mapping(origins, diagnostic);
        diagnostic.source_map_key = mapping.map(|mapping| mapping.key.clone());
        if mapping.is_some_and(|mapping| mapping.producer == SentenceProducer::Raw)
            && diagnostic.code.kind() == CodeKind::Internal
        {
            diagnostic.code = Code::foreign(diagnostic.code.as_str().to_owned(), CodeKind::Author);
        }
    }
}

/// Resolve a native diagnostic's Structured sentence address to its KRS source key.
#[must_use]
pub fn diagnostic_source_map_key(
    origins: &[OriginMapping],
    diagnostic: &FrontendDiagnostic,
) -> Option<SourceMapKey> {
    sentence_mapping(origins, diagnostic).map(|mapping| mapping.key.clone())
}

fn sentence_mapping<'a>(
    origins: &'a [OriginMapping],
    diagnostic: &FrontendDiagnostic,
) -> Option<&'a OriginMapping> {
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
