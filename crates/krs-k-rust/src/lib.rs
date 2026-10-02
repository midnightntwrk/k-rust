//! Versioned adapter to the native `k-rust` frontend.
//!
//! [`compile_definition`] is the route from Definition IR to compiled artifacts.
//! It adapts the IR to a native source definition, prepares it through the pinned frontend's structured loader, compiles it, reparses both KORE definitions, and joins sentence provenance.
//! The route does not parse emitted candidate `.k` source.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt,
};

use k_rust::{
    builtin,
    definition::{
        self as native_definition, Attributes as NativeAttributes, CheckMode as NativeCheckMode,
        FlatImport, FlatModule, ProductionItem as NativeItem, Sentence as NativeSentence,
    },
    diagnostic::{
        Diagnostic as NativeDiagnostic, DiagnosticCode as NativeDiagnosticCode,
        Severity as NativeSeverity,
    },
    kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm},
    kompile,
    kore::parser::parse_definition as parse_kore_definition,
    outer::{LoadOptions as NativeLoadOptions, load_structured},
};
use krs_diagnostic::envelope::DiagnosticGeneratedRange;
use krs_diagnostic::{Code, Diagnostic, Label, Location, Severity, ToDiagnostic, codes};
use krs_ir::{
    ApplicationRef, BuiltinOperation, BuiltinSort, CellAttribute, CellContentFrame, CellPost,
    ClaimModality, ConfigurationRoot, ConfigurationSentence, ContextAliasSentence,
    DefinitionClaimBinder, DefinitionIr, DefinitionProductionAttribute, DefinitionRuleBody,
    DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionTermKind, FixedCell,
    FixedCellContent, FixedConfiguration, FixedConfigurationPattern, FixedConfigurationRewrite,
    FixedConfigurationVariable, FixedInitializerCell, FixedInitializerContent, FormatFragment,
    GrammarProductionItemKind, GroupAssociativity, ListOperation, MapOperation, NodeOrigin,
    OriginFrame, ProductionGroupId, ProductionSentence, RuleSentence, SemanticId, SentenceKind,
    SetOperation, SourceMapKey, StableItemId, StrictnessKind, SymbolId,
};
use serde_json::json;

pub use k_rust::definition::Definition as NativeDefinition;
pub use k_rust::kompile::EmittedSentenceProvenance;
pub use k_rust::outer::LoadedDefinition;
pub use k_rust::provenance::{GeneratingPass, InputAddress, InputSentenceKind, InputSpace};
pub use k_rust::timings::PhaseTimings as NativePhaseTimings;
use krs_ir::measure::Timings;

/// Metadata for the source and builtin revisions forming the native frontend.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FrontendPin {
    /// Cargo package version of the pinned `k-rust` crate.
    pub crate_version: &'static str,
    /// Exact `k-rust` source revision inspected by KRS.
    pub source_revision: &'static str,
    /// K release whose builtin sources are embedded by `k-rust`.
    pub k_version: &'static str,
    /// Exact upstream K source revision embedded by `k-rust`.
    pub k_source_revision: &'static str,
}

/// The native frontend compatibility unit verified by this adapter.
pub const FRONTEND_PIN: FrontendPin = FrontendPin {
    crate_version: "0.4.0",
    source_revision: "f7a2cf1ea842c6f3526bae54540bb268bac1376a",
    k_version: "7.1.337",
    k_source_revision: "4a46d1231473b599c699160132fd6e76a5c46406",
};

/// Backend-specific KORE dialect requested from the frontend.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Backend {
    /// Emit KORE for the LLVM backend.
    #[default]
    Llvm,
    /// Emit symbolic KORE for the Rust backend through the historical Haskell compatibility name.
    Haskell,
}

impl Backend {
    /// Every backend, in command-line catalog order.
    pub const ALL: [Self; 2] = [Self::Llvm, Self::Haskell];

    /// Returns the command-line spelling of this backend.
    #[must_use]
    pub const fn as_str(self) -> &'static str {
        match self {
            Self::Llvm => "llvm",
            Self::Haskell => "haskell",
        }
    }

    /// Returns whether this backend consumes claims.
    ///
    /// Claims are proof obligations. A concrete execution backend has no
    /// prover, so compilation for it omits every claim rather than rejecting
    /// the semantics that carry them.
    #[must_use]
    pub const fn proves_claims(self) -> bool {
        matches!(self, Self::Haskell)
    }
}

/// Capabilities of this adapter build.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FrontendCapabilities {
    /// Backend dialects accepted by [`compile_loaded_definition`].
    pub backends: &'static [Backend],
    /// Availability of Z3-backed ambiguity inference.
    pub z3_inference: CapabilityAvailability,
    /// Availability of MPFR-backed constant folding.
    pub mpfr_folding: CapabilityAvailability,
    /// Availability of KRS-owned invariant-preserving structured `Definition`
    /// preparation over the pinned public primitives.
    pub structured_definition_preparation: CapabilityAvailability,
}

impl FrontendCapabilities {
    /// Returns whether this build can emit KORE for `backend`.
    #[must_use]
    pub fn supports_backend(self, backend: Backend) -> bool {
        self.backends.contains(&backend)
    }
}

/// Availability of an optional native frontend capability.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum CapabilityAvailability {
    /// The capability is compiled in and supported by this adapter.
    Available,
    /// The capability is unavailable for the stated reason.
    Unavailable(&'static str),
}

const SUPPORTED_BACKENDS: &[Backend] = &[Backend::Llvm, Backend::Haskell];

/// Capabilities compiled into the pinned frontend and supplied by this adapter.
pub const FRONTEND_CAPABILITIES: FrontendCapabilities = FrontendCapabilities {
    backends: SUPPORTED_BACKENDS,
    z3_inference: if cfg!(feature = "z3-inference") {
        CapabilityAvailability::Available
    } else {
        CapabilityAvailability::Unavailable("the z3-inference feature is disabled")
    },
    mpfr_folding: CapabilityAvailability::Unavailable(
        "the pinned k-rust dependency is built without mpfr-folding",
    ),
    structured_definition_preparation: CapabilityAvailability::Available,
};

/// Place occupied by one adapted native node.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum NativeNodePlace {
    /// The flat native module itself.
    Module,
    /// A node within a module-local native sentence.
    Sentence {
        /// Module-local native sentence index.
        index: usize,
        /// Structural role within the sentence.
        role: SentenceNodeRole,
    },
}

/// Stable role occupied by a node within an adapted native sentence.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum SentenceNodeRole {
    /// The native sentence itself.
    Sentence,
    /// Cell identity represented inside a configuration sentence.
    ConfigurationCell,
    /// Initializer identity represented inside a configuration sentence.
    ConfigurationInitializer,
    /// Authored name of a context-alias sentence.
    ContextAliasName,
    /// Authored binding selected as `HERE` in a context alias.
    ContextAliasHere,
    /// One cell pattern in a context alias.
    ContextAliasCell(u32),
    /// One explicit associative frame in a context alias.
    ContextAliasFrame(u32),
    /// Named context-alias selection on strictness metadata.
    StrictnessContextAlias,
    /// One selected strictness field.
    StrictnessField(u32),
    /// Result-predicate sort on strictness metadata.
    StrictnessResult,
    /// One grammar production item.
    ProductionItem(u32),
    /// One classified production attribute.
    ProductionAttribute(u32),
    /// One cell clause in a fixed-configuration rule.
    ConfigurationRuleCell(u32),
    /// One explicit frame in a fixed-configuration rule.
    ConfigurationRuleFrame(u32),
    /// One claim binder declaration.
    ClaimBinder(u32),
    /// One claim binder name.
    ClaimBinderName(u32),
    /// One claim binder sort.
    ClaimBinderSort(u32),
    /// A claim modality marker.
    ClaimModality,
    /// A claim circularity marker.
    ClaimCircularity,
    /// A rule applicability condition.
    Requires,
    /// A claim postcondition.
    Ensures,
    /// Structured term. Child indices form a deterministic preorder path from
    /// the sentence body (`0`/`1` for rewrite endpoints and application or
    /// sequence argument indices otherwise).
    Term(Vec<u32>),
}

/// Sidecar seam from an IR origin to its structural native destination.
///
/// Roles within a sentence serve diagnostics and editor mapping.
/// Emitted rule and claim identities join through [`SentenceNodeRole::Sentence`].
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OriginMapping {
    /// Stable key shared with KRS source-map sidecars.
    pub key: SourceMapKey,
    /// Complete authored-to-Definition-IR provenance.
    pub origin: NodeOrigin,
    /// Emitted module name containing the native destination.
    pub module: String,
    /// Structural destination within the native module.
    pub place: NativeNodePlace,
}

/// A native source definition structurally adapted from Definition IR.
///
/// This value is intentionally not a [`LoadedDefinition`]. Its origin sidecar
/// retains exact byte ranges and transformation stacks. Native source
/// attributes retain a portable package-relative source name; a native
/// line/column location is omitted because Definition IR has byte ranges but
/// not source contents from which line/column coordinates could be derived
/// honestly.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct AdaptedDefinition {
    definition: NativeDefinition,
    origins: Vec<OriginMapping>,
    omitted_claims: usize,
}

impl AdaptedDefinition {
    /// Returns the pinned frontend's flat source Definition model.
    #[must_use]
    pub const fn definition(&self) -> &NativeDefinition {
        &self.definition
    }

    /// Returns the stable origin mapping in IR traversal order.
    #[must_use]
    pub fn origins(&self) -> &[OriginMapping] {
        &self.origins
    }

    /// Returns the number of claims left out for a backend that does not prove.
    #[must_use]
    pub const fn omitted_claims(&self) -> usize {
        self.omitted_claims
    }
}

/// Structural Definition-IR adaptation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AdapterError {
    /// A validated symbol reference could not be found while indexing the IR.
    MissingSymbol {
        /// Origin of the referencing node.
        key: SourceMapKey,
        /// Missing stable symbol identity.
        symbol: SymbolId,
    },
    /// A validated nominal reference was absent from the adapter index.
    MissingReference {
        /// Origin of the referencing node.
        key: SourceMapKey,
        /// Reference family.
        kind: &'static str,
        /// Stable target identity.
        target: String,
    },
}

impl ToDiagnostic for AdapterError {
    fn to_diagnostic(&self) -> Diagnostic {
        let (code, key) = match self {
            Self::MissingSymbol { key, .. } => (codes::native::ADAPTER_MISSING_SYMBOL, key),
            Self::MissingReference { key, .. } => (codes::native::ADAPTER_MISSING_REFERENCE, key),
        };
        Diagnostic::error(code, self.to_string(), Location::Definition(key.clone()))
    }
}

impl fmt::Display for AdapterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::MissingSymbol { key, symbol } => write!(
                formatter,
                "Definition IR symbol {symbol} referenced at {key} is absent from the adapter index"
            ),
            Self::MissingReference { key, kind, target } => write!(
                formatter,
                "Definition IR {kind} reference {target:?} at {key} is absent from the adapter index"
            ),
        }
    }
}

impl Error for AdapterError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::MissingSymbol { .. } | Self::MissingReference { .. } => None,
        }
    }
}

/// Options for compiling a prepared definition.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct CompileOptions {
    /// Backend-specific KORE dialect to emit.
    pub backend: Backend,
    /// Pretty-printer width for textual KORE artifacts.
    pub kore_width: usize,
}

impl Default for CompileOptions {
    fn default() -> Self {
        Self {
            backend: Backend::Llvm,
            kore_width: 100,
        }
    }
}

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
    // The upstream enum has no documented stable string spelling.
    // Keep this exhaustive workaround so variant additions and renames require an explicit wire-code decision.
    Code::foreign(match code {
        NativeDiagnosticCode::CellCollectionVarWithoutInitial => "CellCollectionVarWithoutInitial",
        NativeDiagnosticCode::ClaimInDefinition => "ClaimInDefinition",
        NativeDiagnosticCode::DeprecatedAttribute => "DeprecatedAttribute",
        NativeDiagnosticCode::DeprecatedProduction => "DeprecatedProduction",
        NativeDiagnosticCode::DuplicateOverload => "DuplicateOverload",
        NativeDiagnosticCode::DuplicateSentenceLabel => "DuplicateSentenceLabel",
        NativeDiagnosticCode::DuplicateConfigurationCell => "DuplicateConfigurationCell",
        NativeDiagnosticCode::DuplicateKLabel => "DuplicateKLabel",
        NativeDiagnosticCode::DuplicateUserList => "DuplicateUserList",
        NativeDiagnosticCode::FutureError => "FutureError",
        NativeDiagnosticCode::InvalidAnonymousVariable => "InvalidAnonymousVariable",
        NativeDiagnosticCode::InvalidAttribute => "InvalidAttribute",
        NativeDiagnosticCode::InvalidAsPattern => "InvalidAsPattern",
        NativeDiagnosticCode::InvalidBracketProduction => "InvalidBracketProduction",
        NativeDiagnosticCode::InvalidAssociativity => "InvalidAssociativity",
        NativeDiagnosticCode::InvalidCommutativeSimplification => {
            "InvalidCommutativeSimplification"
        }
        NativeDiagnosticCode::InvalidConstantFolding => "InvalidConstantFolding",
        NativeDiagnosticCode::InvalidCellConcretization => "InvalidCellConcretization",
        NativeDiagnosticCode::InvalidContext => "InvalidContext",
        NativeDiagnosticCode::InvalidExistentialVariable => "InvalidExistentialVariable",
        NativeDiagnosticCode::InvalidFunctionPattern => "InvalidFunctionPattern",
        NativeDiagnosticCode::InvalidFreshConstant => "InvalidFreshConstant",
        NativeDiagnosticCode::InvalidFunctionConfiguration => "InvalidFunctionConfiguration",
        NativeDiagnosticCode::InvalidLocalFunction => "InvalidLocalFunction",
        NativeDiagnosticCode::InvalidHole => "InvalidHole",
        NativeDiagnosticCode::InvalidHeatCool => "InvalidHeatCool",
        NativeDiagnosticCode::InvalidListDeclaration => "InvalidListDeclaration",
        NativeDiagnosticCode::InvalidMainCell => "InvalidMainCell",
        NativeDiagnosticCode::InvalidMacroExpansion => "InvalidMacroExpansion",
        NativeDiagnosticCode::InvalidOrPattern => "InvalidOrPattern",
        NativeDiagnosticCode::InvalidRegex => "InvalidRegex",
        NativeDiagnosticCode::InvalidRewrite => "InvalidRewrite",
        NativeDiagnosticCode::InvalidIoStream => "InvalidIoStream",
        NativeDiagnosticCode::IsSortPredicateConflict => "IsSortPredicateConflict",
        NativeDiagnosticCode::InvalidSmtLemma => "InvalidSmtLemma",
        NativeDiagnosticCode::InvalidSemanticCast => "InvalidSemanticCast",
        NativeDiagnosticCode::InvalidSimplification => "InvalidSimplification",
        NativeDiagnosticCode::InvalidStreamCell => "InvalidStreamCell",
        NativeDiagnosticCode::InvalidStrictness => "InvalidStrictness",
        NativeDiagnosticCode::InvalidUnitAttribute => "InvalidUnitAttribute",
        NativeDiagnosticCode::IllegalFunctionOnLhs => "IllegalFunctionOnLhs",
        NativeDiagnosticCode::InconsistentFunctionRuleAttributes => {
            "InconsistentFunctionRuleAttributes"
        }
        NativeDiagnosticCode::MultipleTopSorts => "MultipleTopSorts",
        NativeDiagnosticCode::InvalidTokenProduction => "InvalidTokenProduction",
        NativeDiagnosticCode::InvalidDomainValue => "InvalidDomainValue",
        NativeDiagnosticCode::MarkdownWarning => "MarkdownWarning",
        NativeDiagnosticCode::MissingSyntaxModule => "MissingSyntaxModule",
        NativeDiagnosticCode::ProofModuleRule => "ProofModuleRule",
        NativeDiagnosticCode::ProofModuleSyntax => "ProofModuleSyntax",
        NativeDiagnosticCode::SingletonOverload => "SingletonOverload",
        NativeDiagnosticCode::UnusedVariable => "UnusedVariable",
        NativeDiagnosticCode::UnboundVariable => "UnboundVariable",
        NativeDiagnosticCode::UnadmittedHookNamespace => "UnadmittedHookNamespace",
        NativeDiagnosticCode::UnsupportedExistentialVariable => "UnsupportedExistentialVariable",
        NativeDiagnosticCode::UnsupportedCellBag => "UnsupportedCellBag",
        NativeDiagnosticCode::UndefinedKLabel => "UndefinedKLabel",
        NativeDiagnosticCode::UndeclaredTag => "UndeclaredTag",
        NativeDiagnosticCode::UndefinedSort => "UndefinedSort",
        NativeDiagnosticCode::UnrecognizedAttribute => "UnrecognizedAttribute",
        NativeDiagnosticCode::UnsupportedParametricSort => "UnsupportedParametricSort",
        NativeDiagnosticCode::UnusedSymbol => "UnusedSymbol",
    })
}

/// Textual KORE artifacts emitted by the native frontend.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompiledArtifacts {
    /// Semantics definition consumed by a backend.
    pub definition_kore: String,
    /// Syntax-only definition used by parser tooling.
    pub syntax_definition_kore: String,
    /// Compiled macro rules.
    pub macros_kore: String,
    /// Non-fatal frontend diagnostics.
    pub diagnostics: Vec<FrontendDiagnostic>,
    /// Rule and claim identities joined to KRS source origins.
    pub sentence_provenance: SentenceProvenance,
    /// Claims left out because the backend does not prove them.
    pub omitted_claims: usize,
}

/// Textual KORE artifacts with the native, unjoined input relation.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct RawCompiledArtifacts {
    /// Semantics definition consumed by a backend.
    pub definition_kore: String,
    /// Syntax-only definition used by parser tooling.
    pub syntax_definition_kore: String,
    /// Compiled macro rules.
    pub macros_kore: String,
    /// Non-fatal frontend diagnostics.
    pub diagnostics: Vec<FrontendDiagnostic>,
    /// Native rule and claim relation, keyed by `UNIQUE_ID`.
    pub sentence_provenance: BTreeMap<String, EmittedSentenceProvenance>,
    /// Configuration variable sorts in the compiled main module.
    pub configuration_variables: BTreeMap<String, NativeSort>,
}

/// Frontend source and configuration metadata retained for surface parsing.
#[derive(Clone, Debug)]
pub struct ConfigurationContext {
    /// Prepared frontend definition used by the compiler.
    pub frontend_definition: NativeDefinition,
    /// Configuration variable sorts collected after compiler transformations.
    pub configuration_variables: BTreeMap<String, NativeSort>,
}

/// One input author of an emitted rule or claim.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Author {
    /// A sentence in the KRS Definition IR.
    Krs {
        /// Emitted module name.
        module: String,
        /// Module-local sentence index.
        index: u32,
        /// Input sentence kind before compilation.
        kind: InputSentenceKind,
        /// Complete KRS source origin.
        origin: NodeOrigin,
    },
    /// A sentence in the pinned prelude or builtin closure.
    Builtin {
        /// Native module name.
        module: String,
        /// Module-local sentence index.
        index: u32,
        /// Input sentence kind before compilation.
        kind: InputSentenceKind,
    },
}

/// Provenance of one emitted rule or claim identity.
///
/// Exactly one of nonempty `authors` and `generated_by` is present.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct EmittedProvenance {
    authors: Vec<Author>,
    generated_by: Option<GeneratingPass>,
}

impl EmittedProvenance {
    /// Input authors in the native frontend's order.
    #[must_use]
    pub fn authors(&self) -> &[Author] {
        &self.authors
    }

    /// Generating pass when the identity has no input author.
    #[must_use]
    pub const fn generated_by(&self) -> Option<GeneratingPass> {
        self.generated_by
    }
}

/// `UNIQUE_ID` relation for emitted rules and claims.
///
/// Declarations and generated axioms without a `UNIQUE_ID` are outside this relation.
/// The current native pin may also report execution-definition identities from
/// modules outside the emitted main-module closure; KRS preserves that relation.
#[derive(Clone, Debug, Default, Eq, PartialEq)]
pub struct SentenceProvenance {
    by_id: BTreeMap<String, EmittedProvenance>,
    by_source: BTreeMap<SourceMapKey, Vec<String>>,
}

impl SentenceProvenance {
    /// Look up an emitted rule or claim identity.
    #[must_use]
    pub fn get(&self, id: &str) -> Option<&EmittedProvenance> {
        self.by_id.get(id)
    }

    /// All emitted identities contributed by a KRS source key, in identity order.
    #[must_use]
    pub fn emitted_by(&self, key: &SourceMapKey) -> &[String] {
        self.by_source.get(key).map_or(&[], Vec::as_slice)
    }

    /// Iterate over emitted identities in `UNIQUE_ID` order.
    pub fn iter(&self) -> impl Iterator<Item = (&str, &EmittedProvenance)> {
        self.by_id
            .iter()
            .map(|(id, provenance)| (id.as_str(), provenance))
    }
}

/// Invalid relationship between native input addresses and KRS source sentences.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum ProvenanceError {
    /// Two sentence mappings occupy the same adapted address.
    DuplicateSentenceMapping {
        /// Adapted module name.
        module: String,
        /// Module-local sentence index.
        index: u32,
    },
    /// A structured address has no sentence mapping.
    MissingSentenceMapping(InputAddress),
    /// A compile-space address points into a KRS-authored module.
    LossyCompileAddress(InputAddress),
    /// An address exceeds the module's input sentence count.
    IndexOutOfRange(InputAddress),
    /// The native source kind differs from the corresponding IR sentence.
    KindMismatch {
        /// Input address whose kind differs.
        address: InputAddress,
        /// Kind expected from the IR.
        expected: InputSentenceKind,
        /// Kind reported by the native relation.
        actual: InputSentenceKind,
    },
    /// Native relation lacks a kind for an input address.
    MissingKind(InputAddress),
    /// A native identity has neither authors nor a generating pass, or both.
    InvalidIdentity(String),
}

impl ToDiagnostic for ProvenanceError {
    fn to_diagnostic(&self) -> Diagnostic {
        let code = match self {
            Self::DuplicateSentenceMapping { .. } => codes::native::DUPLICATE_SENTENCE_MAPPING,
            Self::MissingSentenceMapping(_) => codes::native::MISSING_SENTENCE_MAPPING,
            Self::LossyCompileAddress(_) => codes::native::LOSSY_COMPILE_ADDRESS,
            Self::IndexOutOfRange(_) => codes::native::INDEX_OUT_OF_RANGE,
            Self::KindMismatch { .. } => codes::native::KIND_MISMATCH,
            Self::MissingKind(_) => codes::native::MISSING_KIND,
            Self::InvalidIdentity(_) => codes::native::INVALID_IDENTITY,
        };
        Diagnostic::error(code, self.to_string(), Location::None)
    }
}

impl fmt::Display for ProvenanceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::DuplicateSentenceMapping { module, index } => write!(
                formatter,
                "native sentence provenance maps {module} sentence {index} more than once"
            ),
            Self::MissingSentenceMapping(address) => write!(
                formatter,
                "native sentence provenance has no mapping for {}",
                ProvenanceAddress(address)
            ),
            Self::LossyCompileAddress(address) => write!(
                formatter,
                "native sentence provenance cannot map compile address {} to a KRS sentence",
                ProvenanceAddress(address)
            ),
            Self::IndexOutOfRange(address) => write!(
                formatter,
                "native sentence provenance address {} is outside its module",
                ProvenanceAddress(address)
            ),
            Self::KindMismatch {
                address,
                expected,
                actual,
            } => write!(
                formatter,
                "native sentence provenance at {} has kind {}; expected {}",
                ProvenanceAddress(address),
                actual.as_str(),
                expected.as_str()
            ),
            Self::MissingKind(address) => write!(
                formatter,
                "native sentence provenance has no kind for {}",
                ProvenanceAddress(address)
            ),
            Self::InvalidIdentity(id) => write!(
                formatter,
                "native sentence provenance identity {id:?} has an invalid author relation"
            ),
        }
    }
}

struct ProvenanceAddress<'a>(&'a InputAddress);

impl fmt::Display for ProvenanceAddress<'_> {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        let address = self.0;
        write!(
            formatter,
            "{} input, module {}, sentence {}",
            address.input.as_str(),
            address.module,
            address.index
        )
    }
}

impl Error for ProvenanceError {}

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

    fn resolve_diagnostics(&mut self, origins: &[OriginMapping]) {
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

/// Structurally maps schema-9 Definition IR to the pinned native source
/// Definition model.
///
/// Imports remain public, matching ordinary K `imports MODULE`. Sorts,
/// subsorts, production items, constructor labels, rule labels, and terms use
/// the emitted names stored in Definition IR. `KSequence` maps directly to
/// [`NativeTerm::Sequence`]; no injection, `.K`, production ID, or KORE node
/// is manufactured here.
///
/// # Errors
///
/// Returns [`AdapterError`] for unsupported sentence/term positions or an
/// inconsistent symbol index.
pub fn adapt_definition(ir: &DefinitionIr) -> Result<AdaptedDefinition, AdapterError> {
    Adapter::new(ir, true).adapt(ir)
}

/// Adapt Definition IR as compiled for `backend`, omitting every claim when
/// [`Backend::proves_claims`] is false. Sentence indices and origin mappings
/// describe the adapted modules, so they stay consistent with the omission.
///
/// # Errors
///
/// Returns [`AdapterError`] under the same conditions as [`adapt_definition`].
pub fn adapt_definition_for(
    ir: &DefinitionIr,
    backend: Backend,
) -> Result<AdaptedDefinition, AdapterError> {
    Adapter::new(ir, backend.proves_claims()).adapt(ir)
}

/// Prepare one structurally adapted definition through the public structured
/// loader. The loader establishes the bundled prelude, backend filtering,
/// source-file set, configuration expansion, and graph invariants without
/// parsing emitted KRS `.k` source.
///
/// # Errors
///
/// Returns the complete typed rejection when the pinned loader, configuration expander, or resolver rejects the graph.
pub fn prepare_definition(
    definition: NativeDefinition,
    backend: Backend,
) -> Result<LoadedDefinition, PreparationError> {
    let prelude = builtin::embedded("prelude.md").ok_or(PreparationError::MissingPrelude)?;
    let excluded = match backend {
        Backend::Llvm => kompile::CompilationBackend::Llvm.excluded_module_attribute(),
        Backend::Haskell => kompile::CompilationBackend::Rust.excluded_module_attribute(),
    };
    load_structured(
        definition,
        &NativeLoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![excluded.to_owned()],
            ..NativeLoadOptions::default()
        },
    )
    .map_err(PreparationError::from)
}

/// Compile schema-9 Definition IR through the permanent native boundary.
///
/// # Errors
///
/// Returns an adapter, preparation, compilation, or KORE-reparse error without
/// invoking a filesystem-backed K tool or parsing emitted candidate source.
pub fn compile_definition(
    ir: &DefinitionIr,
    options: CompileOptions,
) -> Result<CompiledArtifacts, DefinitionCompileError> {
    compile_definition_timed(ir, options, &mut Timings::disabled())
}

/// [`compile_definition`] recording `native.*` spans in `timings`, with
/// k-rust's own phase list nested unchanged under `native.compile` (see
/// [`krs_ir::measure`]).
///
/// # Errors
///
/// Fails exactly when [`compile_definition`] fails.
pub fn compile_definition_timed(
    ir: &DefinitionIr,
    options: CompileOptions,
    timings: &mut Timings,
) -> Result<CompiledArtifacts, DefinitionCompileError> {
    compile_definition_with_context_timed(ir, options, timings).map(|(artifacts, _)| artifacts)
}

/// Compile Definition IR and retain the matching frontend configuration context.
///
/// # Errors
///
/// Fails exactly when [`compile_definition_timed`] fails.
pub fn compile_definition_with_context_timed(
    ir: &DefinitionIr,
    options: CompileOptions,
    timings: &mut Timings,
) -> Result<(CompiledArtifacts, ConfigurationContext), DefinitionCompileError> {
    let adapted = timings.try_span("native.adapt", |_| {
        adapt_definition_for(ir, options.backend).map_err(DefinitionCompileError::Adapter)
    })?;
    let loaded = timings.try_span("native.prepare", |_| {
        prepare_definition(adapted.definition.clone(), options.backend).map_err(|mut error| {
            error.resolve_diagnostics(adapted.origins());
            DefinitionCompileError::Preparation(error)
        })
    })?;
    let mut artifacts = timings.try_span("native.compile", |timings| {
        let (artifacts, phases) =
            compile_loaded_definition_timed(&loaded, options).map_err(|mut error| {
                resolve_diagnostic_keys(adapted.origins(), &mut error.diagnostics);
                DefinitionCompileError::Compile(error)
            })?;
        for phase in phases.phases {
            timings.record(phase.name, phase.seconds, phase.depth);
        }
        Ok(artifacts)
    })?;
    resolve_diagnostic_keys(adapted.origins(), &mut artifacts.diagnostics);
    timings.try_span("native.reparse.definition", |_| {
        parse_kore_definition(&artifacts.definition_kore).map_err(|error| {
            DefinitionCompileError::KoreReparse {
                artifact: "definition.kore",
                error,
            }
        })
    })?;
    timings.try_span("native.reparse.syntax", |_| {
        parse_kore_definition(&artifacts.syntax_definition_kore).map_err(|error| {
            DefinitionCompileError::KoreReparse {
                artifact: "syntaxDefinition.kore",
                error,
            }
        })
    })?;
    let sentence_provenance = timings.try_span("native.provenance", |_| {
        join_sentence_provenance(ir, &adapted, &loaded, &artifacts.sentence_provenance)
            .map_err(DefinitionCompileError::Provenance)
    })?;
    let context = ConfigurationContext {
        frontend_definition: loaded.definition,
        configuration_variables: artifacts.configuration_variables,
    };
    Ok((
        CompiledArtifacts {
            definition_kore: artifacts.definition_kore,
            syntax_definition_kore: artifacts.syntax_definition_kore,
            macros_kore: artifacts.macros_kore,
            diagnostics: artifacts.diagnostics,
            sentence_provenance,
            omitted_claims: adapted.omitted_claims,
        },
        context,
    ))
}

fn resolve_diagnostic_keys(origins: &[OriginMapping], diagnostics: &mut [FrontendDiagnostic]) {
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

fn input_kind(sentence: &DefinitionSentence) -> InputSentenceKind {
    match sentence {
        DefinitionSentence::SyntaxSort(_) => InputSentenceKind::SyntaxSort,
        DefinitionSentence::Subsort(_) | DefinitionSentence::Production(_) => {
            InputSentenceKind::Production
        }
        DefinitionSentence::Precedence(_) => InputSentenceKind::SyntaxPriority,
        DefinitionSentence::Associativity(_) => InputSentenceKind::SyntaxAssociativity,
        DefinitionSentence::Configuration(_) => InputSentenceKind::Configuration,
        DefinitionSentence::ContextAlias(_) => InputSentenceKind::ContextAlias,
        DefinitionSentence::Rule(rule) if rule.claim().is_some() => InputSentenceKind::Claim,
        DefinitionSentence::Rule(_) => InputSentenceKind::Rule,
    }
}

#[allow(clippy::too_many_lines)] // Validates both address spaces and every sentence kind in one join.
fn join_sentence_provenance(
    ir: &DefinitionIr,
    adapted: &AdaptedDefinition,
    loaded: &LoadedDefinition,
    raw: &BTreeMap<String, EmittedSentenceProvenance>,
) -> Result<SentenceProvenance, ProvenanceError> {
    let modules = ir
        .modules()
        .iter()
        .map(|module| (module.id().as_str(), module))
        .collect::<BTreeMap<_, _>>();
    let mut mappings = BTreeMap::new();
    for mapping in adapted.origins() {
        let NativeNodePlace::Sentence {
            index,
            role: SentenceNodeRole::Sentence,
        } = &mapping.place
        else {
            continue;
        };
        if mappings
            .insert((mapping.module.as_str(), *index), mapping)
            .is_some()
        {
            return Err(ProvenanceError::DuplicateSentenceMapping {
                module: mapping.module.clone(),
                index: u32::try_from(*index).unwrap_or(u32::MAX),
            });
        }
    }
    let mut relation = SentenceProvenance::default();
    for (id, entry) in raw {
        if entry.input_addresses.is_empty() == entry.generated_by.is_none() {
            return Err(ProvenanceError::InvalidIdentity(id.clone()));
        }
        let mut authors = Vec::with_capacity(entry.input_addresses.len());
        for address in &entry.input_addresses {
            let kind = *entry
                .input_sentence_kinds
                .get(address)
                .ok_or_else(|| ProvenanceError::MissingKind(address.clone()))?;
            let index = address.index as usize;
            match address.input {
                InputSpace::Structured => {
                    let Some(module) = modules.get(address.module.as_str()) else {
                        return Err(ProvenanceError::MissingSentenceMapping(address.clone()));
                    };
                    if adapted
                        .definition()
                        .modules
                        .iter()
                        .find(|native_module| native_module.name == address.module)
                        .is_none_or(|native_module| index >= native_module.local_sentences.len())
                    {
                        return Err(ProvenanceError::IndexOutOfRange(address.clone()));
                    }
                    let Some(mapping) = mappings.get(&(address.module.as_str(), index)) else {
                        return Err(ProvenanceError::MissingSentenceMapping(address.clone()));
                    };
                    let Some(sentence) = module
                        .sentences()
                        .iter()
                        .find(|sentence| sentence.origin().key() == &mapping.key)
                    else {
                        return Err(ProvenanceError::IndexOutOfRange(address.clone()));
                    };
                    let expected = input_kind(sentence);
                    if kind != expected {
                        return Err(ProvenanceError::KindMismatch {
                            address: address.clone(),
                            expected,
                            actual: kind,
                        });
                    }
                    authors.push(Author::Krs {
                        module: address.module.clone(),
                        index: address.index,
                        kind,
                        origin: mapping.origin.clone(),
                    });
                    let ids = relation.by_source.entry(mapping.key.clone()).or_default();
                    if !ids.contains(id) {
                        ids.push(id.clone());
                    }
                }
                InputSpace::Compile => {
                    if modules.contains_key(address.module.as_str()) {
                        return Err(ProvenanceError::LossyCompileAddress(address.clone()));
                    }
                    let sentence = loaded
                        .definition
                        .modules
                        .iter()
                        .find(|module| module.name == address.module)
                        .and_then(|module| module.local_sentences.get(index))
                        .ok_or_else(|| ProvenanceError::IndexOutOfRange(address.clone()))?;
                    let expected = InputSentenceKind::of(sentence);
                    if kind != expected {
                        return Err(ProvenanceError::KindMismatch {
                            address: address.clone(),
                            expected,
                            actual: kind,
                        });
                    }
                    authors.push(Author::Builtin {
                        module: address.module.clone(),
                        index: address.index,
                        kind,
                    });
                }
            }
        }
        relation.by_id.insert(
            id.clone(),
            EmittedProvenance {
                authors,
                generated_by: entry.generated_by,
            },
        );
    }
    Ok(relation)
}

/// Failure from a named stage of the native frontend pipeline.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct CompileError {
    diagnostics: Vec<FrontendDiagnostic>,
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

/// Compile an already-prepared native definition to textual KORE and its raw
/// input-address relation.
///
/// `loaded` must have been prepared with the backend-specific module filter
/// returned by `k-rust` and must contain a resolved graph consistent with its
/// flat definition. This adapter intentionally does not expose an unchecked
/// structured-definition preparation shortcut.
/// The raw relation is not joined to KRS origins because this route has no
/// `OriginMapping`; use [`compile_definition`] for the joined relation.
///
/// # Errors
///
/// Returns [`CompileError`] with the precise native pipeline stage and any
/// structured diagnostics when the frontend rejects the definition.
pub fn compile_loaded_definition(
    loaded: &LoadedDefinition,
    options: CompileOptions,
) -> Result<RawCompiledArtifacts, CompileError> {
    compile_loaded_definition_timed(loaded, options).map(|(artifacts, _)| artifacts)
}

/// [`compile_loaded_definition`] that also returns k-rust's wall-clock phase
/// timings in pipeline order. k-rust records them unconditionally, so this
/// costs nothing over the untimed call.
///
/// # Errors
///
/// Fails exactly when [`compile_loaded_definition`] fails.
pub fn compile_loaded_definition_timed(
    loaded: &LoadedDefinition,
    options: CompileOptions,
) -> Result<(RawCompiledArtifacts, NativePhaseTimings), CompileError> {
    let backend = match options.backend {
        Backend::Llvm => kompile::CompilationBackend::Llvm,
        Backend::Haskell => kompile::CompilationBackend::Rust,
    };
    let (artifacts, phases) = kompile::compile_loaded_definition_timed(
        loaded,
        kompile::CompileOptions {
            backend,
            kore_width: options.kore_width,
            default_claims_to_all_path: false,
            hook_namespaces: None,
            // Definition IR represents a self-contained proof unit: when it
            // contains claims, the semantics and specification intentionally
            // share the selected main module. Tell the upstream checker to use
            // its explicit colocated-proof policy; claim-free inputs retain the
            // stricter definition-only policy.
            check_mode: if loaded.definition.modules.iter().any(|module| {
                module
                    .local_sentences
                    .iter()
                    .any(|sentence| matches!(**sentence, NativeSentence::Claim { .. }))
            }) {
                NativeCheckMode::Proof {
                    definition_module: loaded.definition.main_module.clone(),
                }
            } else {
                NativeCheckMode::Definition
            },
            ..kompile::CompileOptions::default()
        },
    )
    .map_err(CompileError::from)?;

    Ok((
        RawCompiledArtifacts {
            definition_kore: artifacts.definition_kore,
            syntax_definition_kore: artifacts.syntax_definition_kore,
            macros_kore: artifacts.macros_kore,
            diagnostics: artifacts.diagnostics.iter().map(Into::into).collect(),
            sentence_provenance: artifacts.sentence_provenance,
            configuration_variables: artifacts.configuration_variables,
        },
        phases,
    ))
}

struct Adapter {
    symbols: BTreeMap<SymbolId, String>,
    groups: BTreeMap<ProductionGroupId, String>,
    context_aliases: BTreeMap<StableItemId, String>,
    cells: BTreeMap<SymbolId, String>,
    initializer_variables: BTreeMap<SemanticId, String>,
    context_here: Option<SemanticId>,
    origins: Vec<OriginMapping>,
    keep_claims: bool,
    omitted_claims: usize,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TermContext {
    Normal,
    ConfigurationInitializer,
    ContextAlias,
}

impl Adapter {
    fn new(ir: &DefinitionIr, keep_claims: bool) -> Self {
        let mut symbols = BTreeMap::new();
        let mut groups = BTreeMap::new();
        let mut context_aliases = BTreeMap::new();
        let mut cells = BTreeMap::new();
        for module in ir.modules() {
            for group in module.production_groups() {
                groups.insert(group.id().clone(), group.emitted_name().to_owned());
            }
            for sentence in module.sentences() {
                match sentence {
                    DefinitionSentence::SyntaxSort(sentence) => {
                        symbols.insert(
                            sentence.symbol().id().clone(),
                            sentence.symbol().emitted_name().to_owned(),
                        );
                    }
                    DefinitionSentence::Production(sentence) => {
                        symbols.insert(
                            sentence.symbol().id().clone(),
                            sentence.symbol().emitted_name().to_owned(),
                        );
                    }
                    DefinitionSentence::Configuration(configuration) => {
                        collect_fixed_cells(configuration.cells(), &mut cells);
                    }
                    DefinitionSentence::ContextAlias(sentence) => {
                        context_aliases.insert(sentence.id().clone(), sentence.name().to_owned());
                    }
                    DefinitionSentence::Subsort(_)
                    | DefinitionSentence::Precedence(_)
                    | DefinitionSentence::Associativity(_)
                    | DefinitionSentence::Rule(_) => {}
                }
            }
        }
        Self {
            symbols,
            groups,
            context_aliases,
            cells,
            initializer_variables: BTreeMap::new(),
            context_here: None,
            origins: Vec::new(),
            keep_claims,
            omitted_claims: 0,
        }
    }

    fn adapt(mut self, ir: &DefinitionIr) -> Result<AdaptedDefinition, AdapterError> {
        let modules = ir
            .modules()
            .iter()
            .map(|module| self.module(module))
            .collect::<Result<Vec<_>, _>>()?;
        Ok(AdaptedDefinition {
            definition: NativeDefinition {
                main_module: ir.main_module().as_str().to_owned(),
                modules,
                attributes: NativeAttributes::default(),
            },
            origins: self.origins,
            omitted_claims: self.omitted_claims,
        })
    }

    fn module(&mut self, module: &krs_ir::DefinitionModule) -> Result<FlatModule, AdapterError> {
        let module_name = module.id().as_str().to_owned();
        self.map_origin(module.origin(), &module_name, NativeNodePlace::Module);
        let mut local_sentences = Vec::with_capacity(module.sentences().len());
        for sentence in module.sentences() {
            if !self.keep_claims
                && matches!(sentence, DefinitionSentence::Rule(rule) if rule.claim().is_some())
            {
                self.omitted_claims += 1;
                continue;
            }
            let sentence_index = local_sentences.len();
            let native = self.sentence(sentence, &module_name, sentence_index)?;
            local_sentences.push(std::sync::Arc::new(native));
        }
        let mut imports = module_builtin_imports(module);
        imports.extend(
            module
                .imports()
                .iter()
                .map(|import| import.as_str().to_owned()),
        );
        Ok(FlatModule {
            name: module_name,
            imports: imports
                .into_iter()
                .map(|name| FlatImport { name, public: true })
                .collect(),
            local_sentences,
            attributes: attributes_for_origin(module.origin()),
        })
    }

    fn sentence(
        &mut self,
        sentence: &DefinitionSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.map_sentence_origin(
            sentence.origin(),
            module,
            sentence_index,
            SentenceNodeRole::Sentence,
        );
        match sentence {
            DefinitionSentence::SyntaxSort(sentence) => Ok(NativeSentence::SyntaxSort {
                parameters: Vec::new(),
                sort: NativeSort::new(sentence.symbol().emitted_name()),
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Subsort(sentence) => Ok(NativeSentence::Production {
                label: None,
                parameters: Vec::new(),
                sort: self.sort(sentence.supersort(), sentence.origin())?,
                items: vec![NativeItem::NonTerminal {
                    sort: self.sort(sentence.subsort(), sentence.origin())?,
                    name: None,
                }],
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Production(sentence) => {
                self.production(sentence, module, sentence_index)
            }
            DefinitionSentence::Precedence(sentence) => Ok(NativeSentence::SyntaxPriority {
                priorities: vec![
                    sentence
                        .higher()
                        .iter()
                        .map(|group| self.group_name(group, sentence.origin()))
                        .collect::<Result<Vec<_>, _>>()?,
                    sentence
                        .lower()
                        .iter()
                        .map(|group| self.group_name(group, sentence.origin()))
                        .collect::<Result<Vec<_>, _>>()?,
                ],
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Associativity(sentence) => {
                Ok(NativeSentence::SyntaxAssociativity {
                    associativity: match sentence.associativity() {
                        GroupAssociativity::Left => native_definition::Associativity::Left,
                        GroupAssociativity::Right => native_definition::Associativity::Right,
                        GroupAssociativity::NonAssociative => {
                            native_definition::Associativity::NonAssoc
                        }
                    },
                    tags: sentence
                        .groups()
                        .iter()
                        .map(|group| self.group_name(group, sentence.origin()))
                        .collect::<Result<Vec<_>, _>>()?,
                    attributes: attributes_for_origin(sentence.origin()),
                })
            }
            DefinitionSentence::Configuration(sentence) => {
                self.configuration(sentence, module, sentence_index)
            }
            DefinitionSentence::ContextAlias(sentence) => {
                self.context_alias(sentence, module, sentence_index)
            }
            DefinitionSentence::Rule(sentence) => self.rule(sentence, module, sentence_index),
        }
    }

    fn production(
        &mut self,
        sentence: &ProductionSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        let mut attributes = attributes_for_origin(sentence.origin());
        for (index, attribute) in sentence.attributes().iter().enumerate() {
            let index = u32::try_from(index).unwrap_or(u32::MAX);
            self.map_sentence_origin(
                attribute.origin(),
                module,
                sentence_index,
                SentenceNodeRole::ProductionAttribute(index),
            );
            self.production_attribute(
                attribute,
                sentence,
                &mut attributes,
                module,
                sentence_index,
                index,
            )?;
        }
        let items = sentence
            .items()
            .iter()
            .enumerate()
            .map(|(index, item)| {
                self.map_sentence_origin(
                    item.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::ProductionItem(u32::try_from(index).unwrap_or(u32::MAX)),
                );
                match item.kind() {
                    GrammarProductionItemKind::Terminal { text } => {
                        Ok(NativeItem::Terminal(text.clone()))
                    }
                    GrammarProductionItemKind::NonTerminal { field, sort } => {
                        Ok(NativeItem::NonTerminal {
                            sort: self.sort(sort, item.origin())?,
                            name: Some(field.as_str().to_owned()),
                        })
                    }
                    GrammarProductionItemKind::RegexTerminal {
                        precede_regex,
                        regex,
                        follow_regex,
                    } => Ok(NativeItem::RegexTerminal {
                        precede_regex: precede_regex.clone(),
                        regex: regex.clone(),
                        follow_regex: follow_regex.clone(),
                    }),
                }
            })
            .collect::<Result<Vec<_>, AdapterError>>()?;
        // token-production-constructor: token values lower to KORE domain
        // values, never applications of their parser production. Omit the
        // unused label to match the source frontend's unlabelled-token form.
        let label = attributes
            .get("token")
            .is_none()
            .then(|| NativeLabel::new(sentence.symbol().emitted_name()));
        Ok(NativeSentence::Production {
            label,
            parameters: Vec::new(),
            sort: self.sort(sentence.result_sort(), sentence.origin())?,
            items,
            attributes,
        })
    }

    #[allow(clippy::too_many_lines)]
    fn production_attribute(
        &mut self,
        attribute: &DefinitionProductionAttribute,
        sentence: &ProductionSentence,
        attributes: &mut NativeAttributes,
        module: &str,
        sentence_index: usize,
        attribute_index: u32,
    ) -> Result<(), AdapterError> {
        match attribute {
            DefinitionProductionAttribute::Documentation { .. } => {}
            DefinitionProductionAttribute::Function { .. } => {
                attributes.insert("function", json!(""));
            }
            DefinitionProductionAttribute::Total { .. } => {
                attributes.insert("total", json!(""));
            }
            DefinitionProductionAttribute::Hook { operation, .. } => {
                let hook = match operation {
                    krs_ir::HookOperation::KryptoKeccak256Raw => "KRYPTO.keccak256raw",
                    krs_ir::HookOperation::KryptoSha256Raw => "KRYPTO.sha256raw",
                    krs_ir::HookOperation::KryptoRipemd160Raw => "KRYPTO.ripemd160raw",
                    krs_ir::HookOperation::KryptoEcdsaRecover => "KRYPTO.ecdsaRecover",
                    krs_ir::HookOperation::KryptoBn128Valid => "KRYPTO.bn128valid",
                    krs_ir::HookOperation::KryptoBn128Add => "KRYPTO.bn128add",
                    krs_ir::HookOperation::KryptoBn128Mul => "KRYPTO.bn128mul",
                    krs_ir::HookOperation::KryptoBn128G2Valid => "KRYPTO.bn128g2valid",
                    krs_ir::HookOperation::KryptoBn128Ate => "KRYPTO.bn128ate",
                };
                attributes.insert("hook", json!(hook));
            }
            DefinitionProductionAttribute::Alias { .. } => {
                attributes.insert("alias", json!(""));
            }
            DefinitionProductionAttribute::Token {
                lexical_precedence, ..
            } => {
                attributes.insert("token", json!(""));
                if let Some(value) = lexical_precedence {
                    attributes.insert("prec", json!(value.to_string()));
                }
            }
            DefinitionProductionAttribute::Group { group, .. } => {
                attributes.insert("group", json!(self.group_name(group, attribute.origin())?));
            }
            DefinitionProductionAttribute::Bracket { .. } => {
                use std::fmt::Write as _;

                attributes.insert("bracket", json!(""));
                let format =
                    (1..=sentence.items().len()).fold(String::new(), |mut output, index| {
                        write!(output, "%{index}").expect("writing to String cannot fail");
                        output
                    });
                attributes.insert("format", json!(format));
            }
            DefinitionProductionAttribute::Avoid { .. } => {
                attributes.insert("avoid", json!(""));
            }
            DefinitionProductionAttribute::Format { fragments, .. } => {
                attributes.insert("format", json!(native_format(fragments)));
            }
            DefinitionProductionAttribute::Strictness {
                kind,
                using,
                fields,
                result_sort,
                ..
            } => {
                let nonterminals = sentence
                    .items()
                    .iter()
                    .filter_map(|item| match item.kind() {
                        GrammarProductionItemKind::NonTerminal { field, .. } => Some(field),
                        _ => None,
                    })
                    .collect::<Vec<_>>();
                let positions = fields
                    .iter()
                    .map(|selected| {
                        nonterminals
                            .iter()
                            .position(|field| **field == *selected.field())
                            .map(|position| position + 1)
                            .ok_or_else(|| AdapterError::MissingReference {
                                key: selected.origin().key().clone(),
                                kind: "production field",
                                target: selected.field().as_str().to_owned(),
                            })
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                for (index, selected) in fields.iter().enumerate() {
                    self.map_sentence_origin(
                        selected.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::StrictnessField(u32::try_from(index).unwrap_or(u32::MAX)),
                    );
                }
                self.map_sentence_origin(
                    result_sort.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::StrictnessResult,
                );
                let selected_all = positions.len() == nonterminals.len()
                    && positions.iter().copied().eq(1..=nonterminals.len());
                let positions = (!selected_all).then(|| {
                    positions
                        .iter()
                        .map(usize::to_string)
                        .collect::<Vec<_>>()
                        .join(",")
                });
                let value = if let Some(using) = using {
                    self.map_sentence_origin(
                        using.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::StrictnessContextAlias,
                    );
                    let alias = self.context_alias_name(using.alias(), using.origin())?;
                    match positions {
                        Some(positions) => format!("{alias}; {positions}"),
                        None => alias,
                    }
                } else {
                    positions.unwrap_or_default()
                };
                attributes.insert(
                    match kind {
                        StrictnessKind::Strict => "strict",
                        StrictnessKind::SeqStrict => "seqstrict",
                    },
                    json!(value),
                );
                if using.is_none() {
                    attributes.insert(
                        "result",
                        json!(self.sort(result_sort.sort(), result_sort.origin())?.name),
                    );
                }
                let _ = attribute_index;
            }
        }
        Ok(())
    }

    fn configuration(
        &mut self,
        configuration: &ConfigurationSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.initializer_variables.clear();
        for variable in configuration.variables() {
            self.initializer_variables
                .insert(variable.id().clone(), variable.external_name().to_owned());
            self.map_sentence_origin(
                variable.origin(),
                module,
                sentence_index,
                SentenceNodeRole::ConfigurationInitializer,
            );
        }
        self.map_sentence_origin(
            configuration.initializer_origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationInitializer,
        );
        let body = self.fixed_configuration(configuration, module, sentence_index)?;
        self.initializer_variables.clear();
        Ok(NativeSentence::Configuration {
            body,
            ensures: truth(),
            attributes: attributes_for_origin(configuration.origin()),
        })
    }

    fn fixed_configuration(
        &mut self,
        configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeTerm, AdapterError> {
        let forest = self.fixed_initializer_forest(
            configuration.cells(),
            configuration.initializer(),
            configuration.variables(),
            module,
            sentence_index,
        )?;
        Ok(match configuration.root() {
            ConfigurationRoot::GeneratedTop => native_cells(forest),
            ConfigurationRoot::Named { origin, name } => {
                self.map_sentence_origin(
                    origin,
                    module,
                    sentence_index,
                    SentenceNodeRole::ConfigurationCell,
                );
                native_config_cell(
                    name,
                    NativeTerm::apply("#cellPropertyListTerminator", Vec::new()),
                    native_cells(forest),
                )
            }
        })
    }

    fn fixed_initializer_forest(
        &mut self,
        cells: &[FixedCell<DefinitionSortRef, SymbolId>],
        initializer: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
        variables: &[FixedConfigurationVariable<DefinitionSortRef>],
        module: &str,
        sentence_index: usize,
    ) -> Result<Vec<NativeTerm>, AdapterError> {
        cells
            .iter()
            .map(|cell| {
                let matching_initializer = initializer
                    .iter()
                    .find(|value| value.cell() == cell.id())
                    .ok_or_else(|| AdapterError::MissingReference {
                        key: cell.origin().key().clone(),
                        kind: "configuration initializer cell",
                        target: cell.id().as_str().to_owned(),
                    })?;
                self.fixed_initializer_cell(
                    cell,
                    matching_initializer,
                    variables,
                    module,
                    sentence_index,
                )
            })
            .collect()
    }

    fn fixed_initializer_cell(
        &mut self,
        cell: &FixedCell<DefinitionSortRef, SymbolId>,
        initializer: &FixedInitializerCell<SymbolId, DefinitionTerm>,
        variables: &[FixedConfigurationVariable<DefinitionSortRef>],
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            cell.origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationCell,
        );
        self.map_sentence_origin(
            initializer.origin(),
            module,
            sentence_index,
            SentenceNodeRole::ConfigurationInitializer,
        );
        let contents = match (cell.content(), initializer.content()) {
            (FixedCellContent::Term { .. }, FixedInitializerContent::Term { term }) => self.term(
                term,
                module,
                sentence_index,
                Vec::new(),
                TermContext::ConfigurationInitializer,
                None,
            )?,
            (
                FixedCellContent::Children { children },
                FixedInitializerContent::Children {
                    children: initialized_children,
                },
            ) => native_cells(self.fixed_initializer_forest(
                children,
                initialized_children,
                variables,
                module,
                sentence_index,
            )?),
            _ => {
                return Err(AdapterError::MissingReference {
                    key: initializer.origin().key().clone(),
                    kind: "configuration initializer shape",
                    target: cell.id().as_str().to_owned(),
                });
            }
        };
        let is_main = variables.iter().any(|variable| {
            variable.is_main() && initializer_contains_variable(initializer, variable.id())
        });
        let properties = native_cell_properties(cell.attributes(), is_main);
        Ok(native_config_cell(cell.name(), properties, contents))
    }

    fn context_alias(
        &mut self,
        sentence: &ContextAliasSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.map_sentence_origin(
            sentence.name_origin(),
            module,
            sentence_index,
            SentenceNodeRole::ContextAliasName,
        );
        self.map_sentence_origin(
            sentence.here_origin(),
            module,
            sentence_index,
            SentenceNodeRole::ContextAliasHere,
        );
        self.context_here = Some(sentence.here().clone());
        let body = self.configuration_pattern(
            sentence.body(),
            module,
            sentence_index,
            TermContext::ContextAlias,
        )?;
        self.context_here = None;
        let mut attributes = attributes_for_origin(sentence.origin());
        attributes.insert("label", json!(sentence.name()));
        // K's source frontend carries this internal marker from a named
        // computation-cell context alias into its generated cool rule.
        attributes.insert("cool-like", json!(""));
        Ok(NativeSentence::ContextAlias {
            body,
            requires: truth(),
            attributes,
        })
    }

    #[allow(clippy::too_many_lines)]
    fn rule(
        &mut self,
        sentence: &RuleSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        let body = match sentence.relational_body() {
            DefinitionRuleBody::Term(term) => self.term(
                term,
                module,
                sentence_index,
                Vec::new(),
                TermContext::Normal,
                Some(sentence),
            )?,
            DefinitionRuleBody::Configuration(rewrite) => {
                self.configuration_rewrite(rewrite, module, sentence_index, sentence)?
            }
        };
        let requires = sentence.requires().map_or_else(
            || Ok(truth()),
            |condition| {
                self.map_sentence_origin(
                    condition.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::Requires,
                );
                self.term(
                    condition.term(),
                    module,
                    sentence_index,
                    Vec::new(),
                    TermContext::Normal,
                    Some(sentence),
                )
            },
        )?;
        let ensures = sentence
            .claim()
            .and_then(|claim| claim.ensures())
            .map_or_else(
                || Ok(truth()),
                |condition| {
                    self.map_sentence_origin(
                        condition.origin(),
                        module,
                        sentence_index,
                        SentenceNodeRole::Ensures,
                    );
                    self.term(
                        condition.term(),
                        module,
                        sentence_index,
                        Vec::new(),
                        TermContext::Normal,
                        Some(sentence),
                    )
                },
            )?;
        let mut attributes = attributes_for_origin(sentence.origin());
        attributes.insert(
            "label",
            json!(native_rule_label(module, sentence.label().emitted_name())),
        );
        if let Some(priority) = sentence.priority() {
            attributes.insert("priority", json!(priority.value().to_string()));
        }
        if let Some(simplification) = sentence.simplification() {
            attributes.insert(
                "simplification",
                json!(
                    simplification
                        .priority()
                        .map_or_else(String::new, |value| value.value().to_string())
                ),
            );
        }
        if let Some(claim) = sentence.claim() {
            self.map_sentence_origin(
                claim.modality_origin(),
                module,
                sentence_index,
                SentenceNodeRole::ClaimModality,
            );
            attributes.insert(claim_modality_attribute(claim.modality()), json!(""));
            if let Some(origin) = claim.circularity_origin() {
                self.map_sentence_origin(
                    origin,
                    module,
                    sentence_index,
                    SentenceNodeRole::ClaimCircularity,
                );
                attributes.insert("circularity", json!(""));
            }
            for (index, binder) in claim
                .universals()
                .iter()
                .chain(claim.existentials())
                .enumerate()
            {
                self.map_claim_binder(binder, module, sentence_index, index);
            }
        }
        if sentence.kind() == SentenceKind::Claim {
            Ok(NativeSentence::Claim {
                body,
                requires,
                ensures,
                attributes,
            })
        } else {
            Ok(NativeSentence::Rule {
                body,
                requires,
                ensures,
                attributes,
            })
        }
    }

    fn map_claim_binder(
        &mut self,
        binder: &DefinitionClaimBinder,
        module: &str,
        sentence_index: usize,
        index: usize,
    ) {
        let index = u32::try_from(index).unwrap_or(u32::MAX);
        for (origin, role) in [
            (binder.origin(), SentenceNodeRole::ClaimBinder(index)),
            (
                binder.name_origin(),
                SentenceNodeRole::ClaimBinderName(index),
            ),
            (
                binder.sort_origin(),
                SentenceNodeRole::ClaimBinderSort(index),
            ),
        ] {
            self.map_sentence_origin(origin, module, sentence_index, role);
        }
    }

    fn configuration_rewrite(
        &mut self,
        rewrite: &FixedConfigurationRewrite<SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
        sentence: &RuleSentence,
    ) -> Result<NativeTerm, AdapterError> {
        let mut cells = rewrite
            .clauses()
            .iter()
            .enumerate()
            .map(|(index, clause)| {
                let index = u32::try_from(index).unwrap_or(u32::MAX);
                self.map_sentence_origin(
                    clause.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::ConfigurationRuleCell(index),
                );
                if let CellContentFrame::KSequenceTail { origin, .. }
                | CellContentFrame::MapRemainder { origin, .. } = clause.frame()
                {
                    self.map_sentence_origin(
                        origin,
                        module,
                        sentence_index,
                        SentenceNodeRole::ConfigurationRuleFrame(index),
                    );
                }
                let before = self.term(
                    clause.before(),
                    module,
                    sentence_index,
                    vec![index],
                    TermContext::Normal,
                    Some(sentence),
                )?;
                let content = match clause.after() {
                    CellPost::Preserve => before,
                    CellPost::Replace { term } => NativeTerm::Rewrite {
                        left: Box::new(before),
                        right: Box::new(self.term(
                            term,
                            module,
                            sentence_index,
                            vec![index, 1],
                            TermContext::Normal,
                            Some(sentence),
                        )?),
                    },
                };
                self.framed_cell(clause.cell(), content, clause.frame(), clause.origin())
            })
            .collect::<Result<Vec<_>, AdapterError>>()?;
        if sentence.claim().is_some() {
            cells.push(native_claim_counter(sentence_index));
        }
        Ok(native_cells(cells))
    }

    fn configuration_pattern(
        &mut self,
        pattern: &FixedConfigurationPattern<SymbolId, DefinitionTerm>,
        module: &str,
        sentence_index: usize,
        context: TermContext,
    ) -> Result<NativeTerm, AdapterError> {
        let cells = pattern
            .cells()
            .iter()
            .enumerate()
            .map(|(index, cell)| {
                let index = u32::try_from(index).unwrap_or(u32::MAX);
                self.map_sentence_origin(
                    cell.origin(),
                    module,
                    sentence_index,
                    SentenceNodeRole::ContextAliasCell(index),
                );
                if let CellContentFrame::KSequenceTail { origin, .. }
                | CellContentFrame::MapRemainder { origin, .. } = cell.frame()
                {
                    self.map_sentence_origin(
                        origin,
                        module,
                        sentence_index,
                        SentenceNodeRole::ContextAliasFrame(index),
                    );
                }
                let cell_content = self.term(
                    cell.pattern(),
                    module,
                    sentence_index,
                    vec![index],
                    context,
                    None,
                )?;
                self.framed_cell(cell.cell(), cell_content, cell.frame(), cell.origin())
            })
            .collect::<Result<Vec<_>, AdapterError>>()?;
        Ok(native_cells(cells))
    }

    fn framed_cell(
        &self,
        cell: &SymbolId,
        content: NativeTerm,
        frame: &CellContentFrame,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        let name = self.cell_name(cell, origin)?;
        let (content, open_right) = match frame {
            CellContentFrame::Exact => (content, false),
            CellContentFrame::KSequenceTail { binding, .. } => {
                binding.as_ref().map_or((content.clone(), true), |binding| {
                    (
                        NativeTerm::sequence([
                            content,
                            native_variable(binding, Some(NativeSort::new("K")), false),
                        ]),
                        false,
                    )
                })
            }
            CellContentFrame::MapRemainder { binding, .. } => {
                binding.as_ref().map_or((content.clone(), true), |binding| {
                    (
                        NativeTerm::apply(
                            "_Map_",
                            vec![
                                content,
                                native_variable(binding, Some(NativeSort::new("Map")), false),
                            ],
                        ),
                        false,
                    )
                })
            }
        };
        Ok(incomplete_cell(name, content, open_right))
    }

    #[allow(clippy::too_many_lines)]
    fn term(
        &mut self,
        term: &DefinitionTerm,
        module: &str,
        sentence_index: usize,
        path: Vec<u32>,
        context: TermContext,
        rule: Option<&RuleSentence>,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_sentence_origin(
            term.origin(),
            module,
            sentence_index,
            SentenceNodeRole::Term(path.clone()),
        );
        match term.kind() {
            DefinitionTermKind::Variable { variable } => {
                if context == TermContext::ContextAlias
                    && self.context_here.as_ref() == Some(variable)
                {
                    return Ok(NativeTerm::variable("HERE"));
                }
                if context == TermContext::ConfigurationInitializer
                    && let Some(name) = self.initializer_variables.get(variable).cloned()
                {
                    let sort = self.sort(term.sort(), term.origin())?;
                    return Ok(NativeTerm::apply(
                        format!("#SemanticCastTo{}", sort.name),
                        vec![NativeTerm::Token {
                            token: format!("${name}"),
                            sort: NativeSort::new("KConfigVar"),
                        }],
                    ));
                }
                let existential = rule.and_then(RuleSentence::claim).is_some_and(|claim| {
                    claim
                        .existentials()
                        .iter()
                        .any(|binder| binder.id() == variable)
                });
                Ok(native_variable(
                    variable,
                    Some(self.sort(term.sort(), term.origin())?),
                    existential,
                ))
            }
            DefinitionTermKind::Application {
                application,
                arguments,
            } => Ok(NativeTerm::Apply {
                label: NativeLabel::new(match application {
                    ApplicationRef::Declared(symbol) => {
                        self.symbol_name(symbol, term.origin())?.to_owned()
                    }
                    ApplicationRef::Builtin(operation) => builtin_label(*operation).to_owned(),
                }),
                arguments: arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            DefinitionTermKind::Token { value } => Ok(NativeTerm::Token {
                token: value.clone(),
                sort: self.sort(term.sort(), term.origin())?,
            }),
            DefinitionTermKind::KSequence { item_sort, items } => {
                self.sort(item_sort, term.origin())?;
                Ok(NativeTerm::sequence(
                    items
                        .iter()
                        .enumerate()
                        .map(|(index, item)| {
                            let mut child_path = path.clone();
                            child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                            self.term(item, module, sentence_index, child_path, context, rule)
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            }
            DefinitionTermKind::Map {
                operation,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let native = Self::map_term(*operation, arguments, term.origin())?;
                if *operation == MapOperation::Get {
                    // semantic-cast-projection-widening: represent a typed
                    // heterogeneous lookup with the project:<Sort> term used
                    // by k-rust's semantic downcast. Keep the Definition IR
                    // result sort explicit.
                    Ok(NativeTerm::apply(
                        format!("project:{}", self.sort(term.sort(), term.origin())?.name),
                        vec![native],
                    ))
                } else {
                    Ok(native)
                }
            }
            DefinitionTermKind::List {
                operation,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                let native = Self::list_term(*operation, arguments, term.origin())?;
                if *operation == ListOperation::Get {
                    Ok(NativeTerm::apply(
                        format!("project:{}", self.sort(term.sort(), term.origin())?.name),
                        vec![native],
                    ))
                } else {
                    Ok(native)
                }
            }
            DefinitionTermKind::Set {
                operation,
                arguments,
            } => {
                let arguments = arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(argument, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Self::set_term(*operation, arguments, term.origin())
            }
            DefinitionTermKind::Cell { cell, children } => {
                let name = self.cell_name(cell, term.origin())?.to_owned();
                let arguments = children
                    .iter()
                    .enumerate()
                    .map(|(index, child)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(child, module, sentence_index, child_path, context, rule)
                    })
                    .collect::<Result<Vec<_>, _>>()?;
                Ok(NativeTerm::apply(format!("<{name}>"), arguments))
            }
            DefinitionTermKind::Rewrite { from, to } => {
                let mut left_path = path.clone();
                left_path.push(0);
                let mut right_path = path;
                right_path.push(1);
                Ok(NativeTerm::Rewrite {
                    left: Box::new(self.term(
                        from,
                        module,
                        sentence_index,
                        left_path,
                        context,
                        rule,
                    )?),
                    right: Box::new(self.term(
                        to,
                        module,
                        sentence_index,
                        right_path,
                        context,
                        rule,
                    )?),
                })
            }
        }
    }

    fn map_term(
        operation: MapOperation,
        arguments: Vec<NativeTerm>,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        match operation {
            MapOperation::Empty if arguments.is_empty() => Ok(NativeTerm::apply(".Map", vec![])),
            MapOperation::Item if !arguments.is_empty() && arguments.len().is_multiple_of(2) => {
                let mut arguments = arguments.into_iter();
                let mut items = std::iter::from_fn(|| {
                    let key = arguments.next()?;
                    let value = arguments.next().expect("validated even map item arity");
                    Some(NativeTerm::apply("_|->_", vec![key, value]))
                });
                let first = items.next().expect("nonempty even argument list");
                Ok(items.fold(first, |left, right| {
                    NativeTerm::apply("_Map_", vec![left, right])
                }))
            }
            MapOperation::Update if arguments.len() == 3 => {
                Ok(NativeTerm::apply("Map:update", arguments))
            }
            MapOperation::Get if arguments.len() == 2 => {
                Ok(NativeTerm::apply("Map:lookup", arguments))
            }
            MapOperation::InKeys if arguments.len() == 2 => Ok(NativeTerm::apply(
                "_in_keys(_)_MAP_Bool_KItem_Map",
                arguments,
            )),
            _ => Err(AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "Map operation arity",
                target: format!("{operation}/{}", arguments.len()),
            }),
        }
    }

    fn list_term(
        operation: ListOperation,
        arguments: Vec<NativeTerm>,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        let label = match (operation, arguments.len()) {
            (ListOperation::Empty, 0) => ".List",
            (ListOperation::Item, 1) => "ListItem",
            (ListOperation::Concat, 2) => "_List_",
            (ListOperation::Get, 2) => "List:get",
            (ListOperation::Update, 3) => "List:set",
            (ListOperation::Size, 1) => "sizeList",
            (ListOperation::Make, 2) => "makeList(_,_)_LIST_List_Int_KItem",
            (ListOperation::Range, 3) => "List:range",
            (ListOperation::UpdateAll, 3) => "updateList(_,_,_)_LIST_List_List_Int_List",
            _ => {
                return Err(AdapterError::MissingReference {
                    key: origin.key().clone(),
                    kind: "List operation arity",
                    target: format!("{operation}/{}", arguments.len()),
                });
            }
        };
        Ok(NativeTerm::apply(label, arguments))
    }

    fn set_term(
        operation: SetOperation,
        arguments: Vec<NativeTerm>,
        origin: &NodeOrigin,
    ) -> Result<NativeTerm, AdapterError> {
        let label = match (operation, arguments.len()) {
            (SetOperation::Empty, 0) => ".Set",
            (SetOperation::Item, 1) => "SetItem",
            (SetOperation::Concat, 2) => "_Set_",
            (SetOperation::Union, 2) => "_|Set__SET_Set_Set_Set",
            (SetOperation::Contains, 2) => "Set:in",
            _ => {
                return Err(AdapterError::MissingReference {
                    key: origin.key().clone(),
                    kind: "Set operation arity",
                    target: format!("{operation}/{}", arguments.len()),
                });
            }
        };
        Ok(NativeTerm::apply(label, arguments))
    }

    fn sort(
        &self,
        sort: &DefinitionSortRef,
        origin: &NodeOrigin,
    ) -> Result<NativeSort, AdapterError> {
        Ok(NativeSort::new(match sort {
            DefinitionSortRef::Declared(symbol) => self.symbol_name(symbol, origin)?,
            DefinitionSortRef::Builtin(sort) => sort.spec().k_name,
        }))
    }

    fn group_name(
        &self,
        group: &ProductionGroupId,
        origin: &NodeOrigin,
    ) -> Result<String, AdapterError> {
        self.groups
            .get(group)
            .cloned()
            .ok_or_else(|| AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "production group",
                target: group.as_str().to_owned(),
            })
    }

    fn context_alias_name(
        &self,
        alias: &StableItemId,
        origin: &NodeOrigin,
    ) -> Result<String, AdapterError> {
        self.context_aliases
            .get(alias)
            .cloned()
            .ok_or_else(|| AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "context alias",
                target: alias.to_string(),
            })
    }

    fn cell_name<'a>(
        &'a self,
        cell: &SymbolId,
        origin: &NodeOrigin,
    ) -> Result<&'a str, AdapterError> {
        self.cells
            .get(cell)
            .map(String::as_str)
            .ok_or_else(|| AdapterError::MissingReference {
                key: origin.key().clone(),
                kind: "configuration cell",
                target: cell.as_str().to_owned(),
            })
    }

    fn symbol_name<'a>(
        &'a self,
        symbol: &SymbolId,
        origin: &NodeOrigin,
    ) -> Result<&'a str, AdapterError> {
        self.symbols
            .get(symbol)
            .map(String::as_str)
            .ok_or_else(|| AdapterError::MissingSymbol {
                key: origin.key().clone(),
                symbol: symbol.clone(),
            })
    }

    fn map_origin(&mut self, origin: &NodeOrigin, module: &str, place: NativeNodePlace) {
        self.origins.push(OriginMapping {
            key: origin.key().clone(),
            origin: origin.clone(),
            module: module.to_owned(),
            place,
        });
    }

    fn map_sentence_origin(
        &mut self,
        origin: &NodeOrigin,
        module: &str,
        index: usize,
        role: SentenceNodeRole,
    ) {
        self.map_origin(origin, module, NativeNodePlace::Sentence { index, role });
    }
}

fn collect_fixed_cells(
    cells: &[FixedCell<DefinitionSortRef, SymbolId>],
    output: &mut BTreeMap<SymbolId, String>,
) {
    for cell in cells {
        output.insert(cell.id().clone(), cell.name().to_owned());
        if let FixedCellContent::Children { children } = cell.content() {
            collect_fixed_cells(children, output);
        }
    }
}

fn module_builtin_imports(module: &krs_ir::DefinitionModule) -> BTreeSet<String> {
    let mut sorts = BTreeSet::new();
    for sentence in module.sentences() {
        match sentence {
            DefinitionSentence::SyntaxSort(_)
            | DefinitionSentence::Precedence(_)
            | DefinitionSentence::Associativity(_) => {}
            DefinitionSentence::Subsort(sentence) => {
                collect_builtin_sort(sentence.subsort(), &mut sorts);
                collect_builtin_sort(sentence.supersort(), &mut sorts);
            }
            DefinitionSentence::Production(sentence) => {
                collect_builtin_sort(sentence.result_sort(), &mut sorts);
                for item in sentence.items() {
                    if let GrammarProductionItemKind::NonTerminal { sort, .. } = item.kind() {
                        collect_builtin_sort(sort, &mut sorts);
                    }
                }
                for attribute in sentence.attributes() {
                    if let DefinitionProductionAttribute::Strictness { result_sort, .. } = attribute
                    {
                        collect_builtin_sort(result_sort.sort(), &mut sorts);
                    }
                }
            }
            DefinitionSentence::Configuration(sentence) => {
                // Configuration expansion lowers external variables through
                // `Map:lookup`, even when no authored cell has sort Map.
                sorts.insert(BuiltinSort::Map);
                collect_fixed_configuration_builtins(sentence, &mut sorts);
            }
            DefinitionSentence::ContextAlias(sentence) => {
                for variable in sentence.variables() {
                    collect_builtin_sort(variable.sort(), &mut sorts);
                }
                for cell in sentence.body().cells() {
                    collect_term_builtins(cell.pattern(), &mut sorts);
                }
            }
            DefinitionSentence::Rule(sentence) => {
                for variable in sentence.variables() {
                    collect_builtin_sort(variable.sort(), &mut sorts);
                }
                match sentence.relational_body() {
                    DefinitionRuleBody::Term(term) => collect_term_builtins(term, &mut sorts),
                    DefinitionRuleBody::Configuration(rewrite) => {
                        for clause in rewrite.clauses() {
                            collect_term_builtins(clause.before(), &mut sorts);
                            if let CellPost::Replace { term } = clause.after() {
                                collect_term_builtins(term, &mut sorts);
                            }
                        }
                    }
                }
                if let Some(condition) = sentence.requires() {
                    collect_term_builtins(condition.term(), &mut sorts);
                }
                if let Some(condition) = sentence.claim().and_then(|claim| claim.ensures()) {
                    collect_term_builtins(condition.term(), &mut sorts);
                }
            }
        }
    }
    sorts
        .into_iter()
        .filter_map(|sort| sort.spec().k_module.map(str::to_owned))
        .collect()
}

fn collect_builtin_sort(sort: &DefinitionSortRef, output: &mut BTreeSet<BuiltinSort>) {
    if let DefinitionSortRef::Builtin(sort) = sort {
        output.insert(*sort);
    }
}

fn collect_term_builtins(term: &DefinitionTerm, output: &mut BTreeSet<BuiltinSort>) {
    collect_builtin_sort(term.sort(), output);
    match term.kind() {
        DefinitionTermKind::Variable { .. } | DefinitionTermKind::Token { .. } => {}
        DefinitionTermKind::Application {
            application,
            arguments,
        } => {
            if let ApplicationRef::Builtin(operation) = application {
                output.insert(operation.result_sort());
                output.extend(operation.argument_sorts().iter().copied());
            }
            for argument in arguments {
                collect_term_builtins(argument, output);
            }
        }
        DefinitionTermKind::KSequence { item_sort, items } => {
            collect_builtin_sort(item_sort, output);
            for item in items {
                collect_term_builtins(item, output);
            }
        }
        DefinitionTermKind::Map { arguments, .. } => {
            output.insert(BuiltinSort::Map);
            for argument in arguments {
                collect_term_builtins(argument, output);
            }
        }
        DefinitionTermKind::List { arguments, .. } => {
            output.insert(BuiltinSort::List);
            for argument in arguments {
                collect_term_builtins(argument, output);
            }
        }
        DefinitionTermKind::Set { arguments, .. } => {
            output.insert(BuiltinSort::Set);
            for argument in arguments {
                collect_term_builtins(argument, output);
            }
        }
        DefinitionTermKind::Rewrite { from, to } => {
            collect_term_builtins(from, output);
            collect_term_builtins(to, output);
        }
        DefinitionTermKind::Cell { children, .. } => {
            for child in children {
                collect_term_builtins(child, output);
            }
        }
    }
}

fn collect_fixed_configuration_builtins(
    configuration: &FixedConfiguration<DefinitionSortRef, SymbolId, DefinitionTerm>,
    output: &mut BTreeSet<BuiltinSort>,
) {
    fn visit_cells(
        values: &[FixedCell<DefinitionSortRef, SymbolId>],
        output: &mut BTreeSet<BuiltinSort>,
    ) {
        for cell in values {
            match cell.content() {
                FixedCellContent::Term { sort } => collect_builtin_sort(sort, output),
                FixedCellContent::Children { children } => visit_cells(children, output),
            }
        }
    }
    fn initializer(
        cells: &[FixedInitializerCell<SymbolId, DefinitionTerm>],
        output: &mut BTreeSet<BuiltinSort>,
    ) {
        for cell in cells {
            match cell.content() {
                FixedInitializerContent::Term { term } => collect_term_builtins(term, output),
                FixedInitializerContent::Children { children } => initializer(children, output),
            }
        }
    }
    visit_cells(configuration.cells(), output);
    for variable in configuration.variables() {
        collect_builtin_sort(variable.sort(), output);
    }
    initializer(configuration.initializer(), output);
}

fn native_format(fragments: &[FormatFragment]) -> String {
    use std::fmt::Write as _;

    let mut output = String::new();
    for fragment in fragments {
        match fragment {
            FormatFragment::Literal(text) => output.push_str(&text.replace('%', "%%")),
            FormatFragment::Item(index) => {
                write!(output, "%{index}").expect("writing to String cannot fail");
            }
            FormatFragment::Newline => output.push_str("%n"),
            FormatFragment::Indent => output.push_str("%i"),
            FormatFragment::Dedent => output.push_str("%d"),
        }
    }
    output
}

fn native_config_cell(name: &str, properties: NativeTerm, contents: NativeTerm) -> NativeTerm {
    let name_token = || NativeTerm::Token {
        token: name.to_owned(),
        sort: NativeSort::new("#CellName"),
    };
    NativeTerm::apply(
        "#configCell",
        vec![name_token(), properties, contents, name_token()],
    )
}

fn native_cells(mut cells: Vec<NativeTerm>) -> NativeTerm {
    match cells.len() {
        0 => NativeTerm::apply("#cells", Vec::new()),
        1 => cells.pop().expect("length is one"),
        _ => NativeTerm::apply("#cells", cells),
    }
}

fn native_claim_counter(sentence_index: usize) -> NativeTerm {
    let sort = Some(NativeSort::new("Int"));
    incomplete_cell(
        "generatedCounter",
        NativeTerm::Rewrite {
            left: Box::new(NativeTerm::Variable {
                name: format!("_KrsCounter{sentence_index}"),
                sort: sort.clone(),
            }),
            right: Box::new(NativeTerm::Variable {
                name: format!("?KrsCounter{sentence_index}"),
                sort,
            }),
        },
        false,
    )
}

fn native_cell_properties(attributes: &[CellAttribute], main: bool) -> NativeTerm {
    let mut properties = attributes
        .iter()
        .map(|attribute| match attribute {
            CellAttribute::Color { value, .. } => ("color", value.as_str()),
            CellAttribute::Multiplicity { value, .. } => ("multiplicity", value.as_str()),
            CellAttribute::CollectionType { value, .. } => ("type", value.as_str()),
        })
        .collect::<Vec<_>>();
    if main {
        properties.push(("maincell", ""));
    }
    properties.into_iter().rev().fold(
        NativeTerm::apply("#cellPropertyListTerminator", Vec::new()),
        |tail, (key, value)| {
            NativeTerm::apply(
                "#cellPropertyList",
                vec![
                    NativeTerm::apply(
                        "#cellProperty",
                        vec![
                            NativeTerm::Token {
                                token: key.to_owned(),
                                sort: NativeSort::new("#CellName"),
                            },
                            NativeTerm::Token {
                                token: serde_json::to_string(value)
                                    .expect("serializing a string cannot fail"),
                                sort: NativeSort::new("KString"),
                            },
                        ],
                    ),
                    tail,
                ],
            )
        },
    )
}

fn initializer_contains_variable(
    initializer: &FixedInitializerCell<SymbolId, DefinitionTerm>,
    variable: &SemanticId,
) -> bool {
    match initializer.content() {
        FixedInitializerContent::Term { term } => term_contains_variable(term, variable),
        FixedInitializerContent::Children { children } => children
            .iter()
            .any(|child| initializer_contains_variable(child, variable)),
    }
}

fn term_contains_variable(term: &DefinitionTerm, variable: &SemanticId) -> bool {
    match term.kind() {
        DefinitionTermKind::Variable {
            variable: candidate,
        } => candidate == variable,
        DefinitionTermKind::Application { arguments, .. }
        | DefinitionTermKind::KSequence {
            items: arguments, ..
        }
        | DefinitionTermKind::Map { arguments, .. }
        | DefinitionTermKind::List { arguments, .. }
        | DefinitionTermKind::Set { arguments, .. } => arguments
            .iter()
            .any(|argument| term_contains_variable(argument, variable)),
        DefinitionTermKind::Cell { children, .. } => children
            .iter()
            .any(|child| term_contains_variable(child, variable)),
        DefinitionTermKind::Rewrite { from, to } => {
            term_contains_variable(from, variable) || term_contains_variable(to, variable)
        }
        DefinitionTermKind::Token { .. } => false,
    }
}

fn incomplete_cell(name: &str, content: NativeTerm, open_right: bool) -> NativeTerm {
    NativeTerm::apply(
        format!("<{name}>"),
        vec![
            NativeTerm::apply("#noDots", Vec::new()),
            content,
            NativeTerm::apply(if open_right { "#dots" } else { "#noDots" }, Vec::new()),
        ],
    )
}

fn native_variable(
    variable: &SemanticId,
    sort: Option<NativeSort>,
    existential: bool,
) -> NativeTerm {
    let name = if existential {
        format!("?{}", variable_name(variable))
    } else if let Some(name) = anonymous_name(variable) {
        name.to_owned()
    } else {
        variable_name(variable)
    };
    NativeTerm::Variable { name, sort }
}

fn variable_name(variable: &SemanticId) -> String {
    use std::fmt::Write as _;

    let mut output = String::from("V");
    for byte in variable.as_str().as_bytes() {
        write!(output, "{byte:02X}").expect("writing to String cannot fail");
    }
    output
}

fn anonymous_name(variable: &SemanticId) -> Option<&str> {
    let (name, ordinal) = variable.as_str().rsplit_once("__krs_")?;
    (name.starts_with('_')
        && name.len() > 1
        && !ordinal.is_empty()
        && ordinal.bytes().all(|byte| byte.is_ascii_digit()))
    .then_some(name)
}

const fn builtin_label(operation: BuiltinOperation) -> &'static str {
    operation.spec().k_label
}

fn native_rule_label(module: &str, emitted_name: &str) -> String {
    // Shared lowering emits this reserved fallback directly as a label
    // attribute. K therefore leaves it unqualified. Authored/named rules and
    // claims pass through K's named-sentence path and acquire the module.
    if emitted_name.starts_with("krsRule_") {
        emitted_name.to_owned()
    } else {
        format!("{module}.{emitted_name}")
    }
}

const fn claim_modality_attribute(modality: ClaimModality) -> &'static str {
    match modality {
        ClaimModality::OnePath => "one-path",
        ClaimModality::AllPaths => "all-path",
    }
}

fn attributes_for_origin(origin: &NodeOrigin) -> NativeAttributes {
    let mut attributes = NativeAttributes::default();
    if let Some(source) = origin
        .origin()
        .frames()
        .iter()
        .find_map(|frame| match frame {
            OriginFrame::Ranged { range, .. } => Some(range.file.package_relative_path()),
            OriginFrame::Transformation { .. } => None,
        })
    {
        attributes.insert(native_definition::SOURCE_ATTRIBUTE, json!(source));
    }
    attributes
}

fn truth() -> NativeTerm {
    NativeTerm::Token {
        token: "true".into(),
        sort: NativeSort::new("Bool"),
    }
}

#[cfg(test)]
mod tests;
