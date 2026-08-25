//! Versioned adapter to the native `k-rust` frontend.
//!
//! [`adapt_definition`] is the permanent structural boundary. The resulting
//! native source definition has not been prepared for compilation:
//! `k-rust` 0.3.0 does not expose an invariant-preserving preparation entry
//! point. [`compile_definition`] therefore reports that missing capability
//! instead of manufacturing a [`LoadedDefinition`] through public fields.
//!
//! [`compile_definition_provisional_oracle`] exists only as an explicitly
//! provisional M2 oracle. It parses no K source (and in particular never
//! parses emitted candidate `.k`); it uses the public configuration-expansion
//! and graph-resolution passes before isolating the unavoidable public-field
//! assembly in one function.

use std::{collections::BTreeMap, error::Error, fmt};

use k_rust::{
    definition::{
        self as native_definition, Attributes as NativeAttributes, FlatImport, FlatModule,
        ProductionItem as NativeItem, ResolvedDefinition, Sentence as NativeSentence,
        expand_configurations,
    },
    diagnostic::{Diagnostic as NativeDiagnostic, Severity as NativeSeverity},
    kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm},
    kompile,
    kore::parser::parse_definition as parse_kore_definition,
};
use krs_ir::{
    DefinitionIr, DefinitionSentence, DefinitionSortRef, DefinitionTerm, DefinitionTermKind,
    NodeOrigin, OriginFrame, ProductionItem, SentenceKind, SourceMapKey, SymbolId,
};
use serde_json::json;

pub use k_rust::outer::LoadedDefinition;
pub use k_rust::definition::Definition as NativeDefinition;

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
    crate_version: "0.3.0",
    source_revision: "58f33885b736148dae189623d1aac989ce9be475",
    k_version: "7.1.337",
    k_source_revision: "4a46d1231473b599c699160132fd6e76a5c46406",
};

/// Backend-specific KORE dialect requested from the frontend.
#[derive(Clone, Copy, Debug, Default, Eq, PartialEq)]
pub enum Backend {
    /// Emit KORE for the LLVM backend.
    #[default]
    Llvm,
    /// Emit KORE for the Haskell backend.
    Haskell,
}

/// Capabilities of this portable adapter build.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct FrontendCapabilities {
    /// Backend dialects accepted by [`compile_loaded_definition`].
    pub backends: &'static [Backend],
    /// Availability of Z3-backed ambiguity inference.
    pub z3_inference: CapabilityAvailability,
    /// Availability of MPFR-backed constant folding.
    pub mpfr_folding: CapabilityAvailability,
    /// Availability of invariant-preserving structured `Definition` preparation.
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

impl CapabilityAvailability {
    /// Returns whether the capability is available.
    #[must_use]
    pub const fn is_available(self) -> bool {
        matches!(self, Self::Available)
    }
}

const SUPPORTED_BACKENDS: &[Backend] = &[Backend::Llvm, Backend::Haskell];

/// Capabilities compiled into the portable, default-feature-free frontend.
pub const FRONTEND_CAPABILITIES: FrontendCapabilities = FrontendCapabilities {
    backends: SUPPORTED_BACKENDS,
    z3_inference: CapabilityAvailability::Unavailable(
        "the pinned k-rust dependency is built without z3-inference",
    ),
    mpfr_folding: CapabilityAvailability::Unavailable(
        "the pinned k-rust dependency is built without mpfr-folding",
    ),
    structured_definition_preparation: CapabilityAvailability::Unavailable(
        "k-rust 0.3.0 has no public structured Definition preparation entry point",
    ),
};

/// Import policy of the portable provisional M2 preparation route.
///
/// The route does not synthesize the Java frontend's implicit public `MAP`
/// import. Consequently local M2 source sentences can agree while the full
/// imported source/KORE closure remains different (the observed oracle counts
/// are 251 reference sentences versus 130 portable-native sentences).
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortablePreludePolicy {
    /// Preserve only imports present in Definition IR.
    ExplicitImportsOnly,
}

/// Prelude policy used by [`compile_definition_provisional_oracle`].
pub const PORTABLE_PRELUDE_POLICY: PortablePreludePolicy =
    PortablePreludePolicy::ExplicitImportsOnly;

/// Stable role occupied by one adapted native node.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub enum NativeNodeRole {
    /// Flat native module.
    Module,
    /// Flat native sentence at the recorded index.
    Sentence,
    /// Cell identity represented inside a configuration sentence.
    ConfigurationCell,
    /// Initializer identity represented inside a configuration sentence.
    ConfigurationInitializer,
    /// Structured term. Child indices form a deterministic preorder path from
    /// the sentence body (`0`/`1` for rewrite endpoints and application or
    /// sequence argument indices otherwise).
    Term(Vec<u32>),
}

/// Sidecar seam from an IR origin to its structural native destination.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct OriginMapping {
    /// Stable key shared with KRS source-map sidecars.
    pub key: SourceMapKey,
    /// Complete authored-to-Definition-IR provenance.
    pub origin: NodeOrigin,
    /// Emitted module name containing the native destination.
    pub module: String,
    /// Module-local native sentence index, absent for the module itself.
    pub sentence_index: Option<usize>,
    /// Structural role within the module or sentence.
    pub role: NativeNodeRole,
}

#[derive(Clone, Debug, Eq, PartialEq)]
struct InitializerIdentity {
    module: String,
    cell_name: String,
    emitted_name: String,
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
    initializers: Vec<InitializerIdentity>,
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
}

/// A native capability that the frozen M2 adapter cannot preserve.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CapabilityError {
    /// The pinned frontend has no supported structured preparation boundary.
    StructuredDefinitionPreparationUnavailable,
    /// M2 native lowering supports transition rules only.
    UnsupportedSentenceKind {
        /// Origin of the unsupported sentence.
        key: SourceMapKey,
        /// Explicit IR sentence kind.
        kind: SentenceKind,
    },
    /// A term shape is legal in broader Definition IR but not in the M2
    /// position where it occurred.
    UnsupportedTermKind {
        /// Origin of the unsupported nested term.
        key: SourceMapKey,
        /// Stable term-kind name.
        kind: &'static str,
        /// Position-specific capability reason.
        reason: &'static str,
    },
    /// The M2 native configuration route cannot preserve declared
    /// initializer parameters.
    ConfigurationInitializerVariables {
        /// Origin of the initializer declaration.
        key: SourceMapKey,
    },
}

impl fmt::Display for CapabilityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StructuredDefinitionPreparationUnavailable => formatter.write_str(
                "k-rust 0.3.0 has no public invariant-preserving structured Definition preparation API",
            ),
            Self::UnsupportedSentenceKind { key, kind } => write!(
                formatter,
                "native M2 adapter does not support {kind:?} sentence at {:?}",
                key.as_str()
            ),
            Self::UnsupportedTermKind { key, kind, reason } => write!(
                formatter,
                "native M2 adapter does not support {kind} term at {:?}: {reason}",
                key.as_str()
            ),
            Self::ConfigurationInitializerVariables { key } => write!(
                formatter,
                "native M2 adapter cannot preserve initializer variables at {:?}",
                key.as_str()
            ),
        }
    }
}

impl Error for CapabilityError {}

/// Structural Definition-IR adaptation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AdapterError {
    /// A known M2 capability boundary was crossed.
    Capability(CapabilityError),
    /// A validated symbol reference could not be found while indexing the IR.
    MissingSymbol {
        /// Origin of the referencing node.
        key: SourceMapKey,
        /// Missing stable symbol identity.
        symbol: SymbolId,
    },
}

impl fmt::Display for AdapterError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Capability(error) => error.fmt(formatter),
            Self::MissingSymbol { key, symbol } => write!(
                formatter,
                "Definition IR symbol {:?} referenced at {:?} is absent from the adapter index",
                symbol.as_str(),
                key.as_str()
            ),
        }
    }
}

impl Error for AdapterError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Capability(error) => Some(error),
            Self::MissingSymbol { .. } => None,
        }
    }
}

impl From<CapabilityError> for AdapterError {
    fn from(error: CapabilityError) -> Self {
        Self::Capability(error)
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
    pub code: String,
    /// Human-readable diagnostic message.
    pub message: String,
    /// Source identifier, when attached to the originating sentence.
    pub source: Option<String>,
    /// Source location, when attached to the originating sentence.
    pub location: Option<SourceLocation>,
}

impl From<&NativeDiagnostic> for FrontendDiagnostic {
    fn from(diagnostic: &NativeDiagnostic) -> Self {
        Self {
            severity: match diagnostic.severity {
                NativeSeverity::Error => DiagnosticSeverity::Error,
                NativeSeverity::Warning => DiagnosticSeverity::Warning,
            },
            code: format!("{:?}", diagnostic.code),
            message: diagnostic.message.clone(),
            source: diagnostic.source.clone(),
            location: diagnostic.location.map(|location| SourceLocation {
                start_line: location.start_line,
                start_column: location.start_column,
                end_line: location.end_line,
                end_column: location.end_column,
            }),
        }
    }
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
}

/// Permanent structured compilation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DefinitionCompileError {
    /// Definition IR could not be represented by the M2 adapter.
    Adapter(AdapterError),
    /// The adapted source Definition cannot be prepared through a supported
    /// pinned-frontend API.
    Capability(CapabilityError),
}

impl fmt::Display for DefinitionCompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Adapter(error) => error.fmt(formatter),
            Self::Capability(error) => error.fmt(formatter),
        }
    }
}

impl Error for DefinitionCompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Adapter(error) => Some(error),
            Self::Capability(error) => Some(error),
        }
    }
}

/// Failure from the explicitly provisional M2 oracle route.
#[derive(Clone, Debug)]
pub enum ProvisionalCompileError {
    /// Definition IR could not be adapted.
    Adapter(AdapterError),
    /// Public configuration expansion rejected the structured sentence.
    Configuration(String),
    /// The expanded flat module graph was invalid.
    Resolution(String),
    /// The ordered native compilation pipeline rejected the definition.
    Compile(CompileError),
    /// One emitted KORE artifact was not accepted by the pinned KORE parser.
    KoreReparse {
        /// Artifact which failed (`definition.kore` or
        /// `syntaxDefinition.kore`).
        artifact: &'static str,
        /// Pinned parser message.
        message: String,
    },
    /// Configuration expansion did not expose the one generated initializer
    /// identity which must be rebound to the IR-owned emitted name.
    InitializerIdentity {
        /// Module containing the configuration.
        module: String,
        /// Explanation of the unexpected expanded shape.
        message: String,
    },
}

impl fmt::Display for ProvisionalCompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Adapter(error) => error.fmt(formatter),
            Self::Configuration(message) => {
                write!(formatter, "structured configuration expansion failed: {message}")
            }
            Self::Resolution(message) => {
                write!(formatter, "expanded native definition resolution failed: {message}")
            }
            Self::Compile(error) => error.fmt(formatter),
            Self::KoreReparse { artifact, message } => {
                write!(formatter, "pinned parser rejected {artifact}: {message}")
            }
            Self::InitializerIdentity { module, message } => write!(
                formatter,
                "cannot preserve initializer identity in module {module:?}: {message}"
            ),
        }
    }
}

impl Error for ProvisionalCompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Adapter(error) => Some(error),
            Self::Compile(error) => Some(error),
            Self::Configuration(_)
            | Self::Resolution(_)
            | Self::KoreReparse { .. }
            | Self::InitializerIdentity { .. } => None,
        }
    }
}

/// Structurally maps frozen M2 Definition IR to the pinned native source
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
    Adapter::new(ir).adapt(ir)
}

/// Refuses to compile a structural Definition until the pinned frontend has a
/// supported invariant-preserving preparation entry point.
///
/// # Errors
///
/// Returns an adapter capability error first when the IR is outside M2;
/// otherwise always returns
/// [`CapabilityError::StructuredDefinitionPreparationUnavailable`].
pub fn compile_definition(
    ir: &DefinitionIr,
    _options: CompileOptions,
) -> Result<CompiledArtifacts, DefinitionCompileError> {
    adapt_definition(ir).map_err(DefinitionCompileError::Adapter)?;
    Err(DefinitionCompileError::Capability(
        CapabilityError::StructuredDefinitionPreparationUnavailable,
    ))
}

/// Provisional M2 test-oracle compilation through public frontend passes.
///
/// This function parses **no source fragment**. In particular, emitted
/// candidate `.k` is never an input. It structurally adapts Definition IR,
/// invokes the public configuration expander, verifies that the expander's one
/// generated initializer label equals the IR-owned emitted name, resolves the
/// flat graph, and isolates public-field `LoadedDefinition` assembly here.
/// Both returned KORE definitions are reparsed before success is reported.
///
/// This route preserves explicit IR imports only. It does not synthesize
/// `MAP`, so its full KORE closure is not equivalent to a reference route that
/// implicitly imports the pinned prelude.
///
/// # Errors
///
/// Returns [`ProvisionalCompileError`] for adaptation, preparation,
/// compilation, initializer-identity, or KORE-reparse failures.
pub fn compile_definition_provisional_oracle(
    ir: &DefinitionIr,
    options: CompileOptions,
) -> Result<CompiledArtifacts, ProvisionalCompileError> {
    let adapted = adapt_definition(ir).map_err(ProvisionalCompileError::Adapter)?;
    let loaded = prepare_provisional_oracle(adapted)?;
    let artifacts = compile_loaded_definition(&loaded, options)
        .map_err(ProvisionalCompileError::Compile)?;
    parse_kore_definition(&artifacts.definition_kore).map_err(|error| {
        ProvisionalCompileError::KoreReparse {
            artifact: "definition.kore",
            message: error.to_string(),
        }
    })?;
    parse_kore_definition(&artifacts.syntax_definition_kore).map_err(|error| {
        ProvisionalCompileError::KoreReparse {
            artifact: "syntaxDefinition.kore",
            message: error.to_string(),
        }
    })?;
    Ok(artifacts)
}

/// Failure from a named stage of the native frontend pipeline.
#[derive(Clone, Debug)]
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
            "native frontend stage {:?} failed: {}",
            self.source.stage, self.source.message
        )
    }
}

impl Error for CompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        Some(self.source.as_ref())
    }
}

/// Compile an already-prepared native definition to textual KORE.
///
/// `loaded` must have been prepared with the backend-specific module filter
/// returned by `k-rust` and must contain a resolved graph consistent with its
/// flat definition. This adapter intentionally does not expose an unchecked
/// structured-definition preparation shortcut.
///
/// # Errors
///
/// Returns [`CompileError`] with the precise native pipeline stage and any
/// structured diagnostics when the frontend rejects the definition.
pub fn compile_loaded_definition(
    loaded: &LoadedDefinition,
    options: CompileOptions,
) -> Result<CompiledArtifacts, CompileError> {
    let backend = match options.backend {
        Backend::Llvm => kompile::CompilationBackend::Llvm,
        Backend::Haskell => kompile::CompilationBackend::Haskell,
    };
    let artifacts = kompile::compile_loaded_definition(
        loaded,
        kompile::CompileOptions {
            backend,
            kore_width: options.kore_width,
        },
    )
    .map_err(CompileError::from)?;

    Ok(CompiledArtifacts {
        definition_kore: artifacts.definition_kore,
        syntax_definition_kore: artifacts.syntax_definition_kore,
        macros_kore: artifacts.macros_kore,
        diagnostics: artifacts.diagnostics.iter().map(Into::into).collect(),
    })
}

struct Adapter {
    symbols: BTreeMap<SymbolId, String>,
    origins: Vec<OriginMapping>,
    initializers: Vec<InitializerIdentity>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TermContext {
    Normal,
    RuleRoot,
    ConfigurationInitializer,
}

impl Adapter {
    fn new(ir: &DefinitionIr) -> Self {
        let mut symbols = BTreeMap::new();
        for sentence in ir
            .modules()
            .iter()
            .flat_map(|module| module.sentences())
        {
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
                DefinitionSentence::Configuration(sentence) => {
                    symbols.insert(
                        sentence.cell().symbol().id().clone(),
                        sentence.cell().symbol().emitted_name().to_owned(),
                    );
                    symbols.insert(
                        sentence.initializer().symbol().id().clone(),
                        sentence.initializer().symbol().emitted_name().to_owned(),
                    );
                }
                DefinitionSentence::Subsort(_) | DefinitionSentence::Rule(_) => {}
            }
        }
        Self {
            symbols,
            origins: Vec::new(),
            initializers: Vec::new(),
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
            initializers: self.initializers,
        })
    }

    fn module(&mut self, module: &krs_ir::DefinitionModule) -> Result<FlatModule, AdapterError> {
        let module_name = module.id().as_str().to_owned();
        self.map_origin(
            module.origin(),
            &module_name,
            None,
            NativeNodeRole::Module,
        );
        let mut local_sentences = Vec::with_capacity(module.sentences().len());
        for sentence in module.sentences() {
            let sentence_index = local_sentences.len();
            let native = self.sentence(sentence, &module_name, sentence_index)?;
            local_sentences.push(native);
        }
        Ok(FlatModule {
            name: module_name,
            imports: module
                .imports()
                .iter()
                .map(|import| FlatImport {
                    name: import.as_str().to_owned(),
                    public: true,
                })
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
        self.map_origin(
            sentence.origin(),
            module,
            Some(sentence_index),
            NativeNodeRole::Sentence,
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
                sort: NativeSort::new(self.symbol_name(
                    sentence.supersort(),
                    sentence.origin(),
                )?),
                items: vec![NativeItem::NonTerminal {
                    sort: NativeSort::new(self.symbol_name(
                        sentence.subsort(),
                        sentence.origin(),
                    )?),
                    name: None,
                }],
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Production(sentence) => Ok(NativeSentence::Production {
                label: Some(NativeLabel::new(sentence.symbol().emitted_name())),
                parameters: Vec::new(),
                sort: NativeSort::new(
                    self.symbol_name(sentence.result_sort(), sentence.origin())?,
                ),
                items: sentence
                    .items()
                    .iter()
                    .map(|item| match item {
                        ProductionItem::Terminal { text } => {
                            Ok(NativeItem::Terminal(text.clone()))
                        }
                        ProductionItem::NonTerminal { sort } => Ok(NativeItem::NonTerminal {
                            sort: NativeSort::new(self.symbol_name(sort, sentence.origin())?),
                            name: None,
                        }),
                    })
                    .collect::<Result<Vec<_>, AdapterError>>()?,
                attributes: attributes_for_origin(sentence.origin()),
            }),
            DefinitionSentence::Configuration(sentence) => {
                if !sentence.initializer().variables().is_empty() {
                    return Err(CapabilityError::ConfigurationInitializerVariables {
                        key: sentence.initializer().origin().key().clone(),
                    }
                    .into());
                }
                self.map_origin(
                    sentence.cell().origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ConfigurationCell,
                );
                self.map_origin(
                    sentence.initializer().origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ConfigurationInitializer,
                );
                let cell_name = sentence.cell().symbol().emitted_name().to_owned();
                let body = self.term(
                    sentence.initializer().body(),
                    module,
                    sentence_index,
                    Vec::new(),
                    TermContext::ConfigurationInitializer,
                )?;
                self.initializers.push(InitializerIdentity {
                    module: module.to_owned(),
                    cell_name: cell_name.clone(),
                    emitted_name: sentence.initializer().symbol().emitted_name().to_owned(),
                });
                let cell_name_token = || NativeTerm::Token {
                    token: cell_name.clone(),
                    sort: NativeSort::new("#CellName"),
                };
                Ok(NativeSentence::Configuration {
                    body: NativeTerm::apply(
                        "#configCell",
                        vec![
                            cell_name_token(),
                            NativeTerm::apply("#cellPropertyListTerminator", Vec::new()),
                            body,
                            cell_name_token(),
                        ],
                    ),
                    ensures: truth(),
                    attributes: attributes_for_origin(sentence.origin()),
                })
            }
            DefinitionSentence::Rule(sentence) => {
                if sentence.kind() != SentenceKind::Transition {
                    return Err(CapabilityError::UnsupportedSentenceKind {
                        key: sentence.origin().key().clone(),
                        kind: sentence.kind(),
                    }
                    .into());
                }
                let mut attributes = attributes_for_origin(sentence.origin());
                attributes.insert("label", json!(sentence.label().emitted_name()));
                Ok(NativeSentence::Rule {
                    body: self.term(
                        sentence.body(),
                        module,
                        sentence_index,
                        Vec::new(),
                        TermContext::RuleRoot,
                    )?,
                    requires: truth(),
                    ensures: truth(),
                    attributes,
                })
            }
        }
    }

    fn term(
        &mut self,
        term: &DefinitionTerm,
        module: &str,
        sentence_index: usize,
        path: Vec<u32>,
        context: TermContext,
    ) -> Result<NativeTerm, AdapterError> {
        self.map_origin(
            term.origin(),
            module,
            Some(sentence_index),
            NativeNodeRole::Term(path.clone()),
        );
        match term.kind() {
            DefinitionTermKind::Variable { variable } => {
                let DefinitionSortRef::Declared(sort) = term.sort() else {
                    return Err(CapabilityError::UnsupportedTermKind {
                        key: term.origin().key().clone(),
                        kind: "variable",
                        reason: "variables of builtin KSequence sort are outside M2",
                    }
                    .into());
                };
                Ok(NativeTerm::Variable {
                    name: variable.as_str().to_owned(),
                    sort: Some(NativeSort::new(self.symbol_name(sort, term.origin())?)),
                })
            }
            DefinitionTermKind::Application { symbol, arguments } => Ok(NativeTerm::Apply {
                label: NativeLabel::new(self.symbol_name(symbol, term.origin())?),
                arguments: arguments
                    .iter()
                    .enumerate()
                    .map(|(index, argument)| {
                        let mut child_path = path.clone();
                        child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                        self.term(
                            argument,
                            module,
                            sentence_index,
                            child_path,
                            TermContext::Normal,
                        )
                    })
                    .collect::<Result<Vec<_>, _>>()?,
            }),
            DefinitionTermKind::Token { value } => {
                let DefinitionSortRef::Declared(sort) = term.sort() else {
                    return Err(CapabilityError::UnsupportedTermKind {
                        key: term.origin().key().clone(),
                        kind: "token",
                        reason: "tokens of builtin KSequence sort are outside M2",
                    }
                    .into());
                };
                Ok(NativeTerm::Token {
                    token: value.clone(),
                    sort: NativeSort::new(self.symbol_name(sort, term.origin())?),
                })
            }
            DefinitionTermKind::KSequence { item_sort, items } => {
                self.symbol_name(item_sort, term.origin())?;
                Ok(NativeTerm::sequence(
                    items
                        .iter()
                        .enumerate()
                        .map(|(index, item)| {
                            let mut child_path = path.clone();
                            child_path.push(u32::try_from(index).unwrap_or(u32::MAX));
                            self.term(
                                item,
                                module,
                                sentence_index,
                                child_path,
                                TermContext::Normal,
                            )
                        })
                        .collect::<Result<Vec<_>, _>>()?,
                ))
            }
            DefinitionTermKind::Rewrite { from, to } => {
                if context != TermContext::RuleRoot {
                    return Err(CapabilityError::UnsupportedTermKind {
                        key: term.origin().key().clone(),
                        kind: "rewrite",
                        reason: "M2 supports a rewrite only as the root of a transition rule",
                    }
                    .into());
                }
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
                        TermContext::Normal,
                    )?),
                    right: Box::new(self.term(
                        to,
                        module,
                        sentence_index,
                        right_path,
                        TermContext::Normal,
                    )?),
                })
            }
        }
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

    fn map_origin(
        &mut self,
        origin: &NodeOrigin,
        module: &str,
        sentence_index: Option<usize>,
        role: NativeNodeRole,
    ) {
        self.origins.push(OriginMapping {
            key: origin.key().clone(),
            origin: origin.clone(),
            module: module.to_owned(),
            sentence_index,
            role,
        });
    }
}

fn attributes_for_origin(origin: &NodeOrigin) -> NativeAttributes {
    let mut attributes = NativeAttributes::default();
    if let Some(source) = origin.origin().frames().iter().find_map(|frame| match frame {
        OriginFrame::Ranged { range, .. } => Some(range.file.package_relative_path()),
        OriginFrame::Transformation { .. } => None,
    }) {
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

fn prepare_provisional_oracle(
    adapted: AdaptedDefinition,
) -> Result<LoadedDefinition, ProvisionalCompileError> {
    let definition = expand_configurations(&adapted.definition)
        .map_err(|error| ProvisionalCompileError::Configuration(error.to_string()))?;
    for initializer in &adapted.initializers {
        validate_initializer_identity(&definition, initializer)?;
    }
    let resolved = ResolvedDefinition::resolve(&definition)
        .map_err(|error| ProvisionalCompileError::Resolution(error.to_string()))?;
    // This unchecked public-field boundary is deliberately isolated in this
    // provisional oracle. It must be deleted when k-rust exposes supported
    // structured preparation.
    Ok(LoadedDefinition {
        files: Vec::new(),
        definition,
        resolved,
    })
}

fn validate_initializer_identity(
    definition: &NativeDefinition,
    initializer: &InitializerIdentity,
) -> Result<(), ProvisionalCompileError> {
    let Some(module) = definition
        .modules
        .iter()
        .find(|module| module.name == initializer.module)
    else {
        return Err(ProvisionalCompileError::InitializerIdentity {
            module: initializer.module.clone(),
            message: "expanded module is absent".into(),
        });
    };
    let cell_sort = native_definition::configuration::cell_sort_name(&initializer.cell_name);
    let generated = module
        .local_sentences
        .iter()
        .filter_map(|sentence| match sentence {
            NativeSentence::Production {
                label: Some(label),
                sort,
                attributes,
                ..
            } if sort.name == cell_sort && attributes.get("initializer").is_some() => {
                Some(label.name.clone())
            }
            _ => None,
        })
        .collect::<Vec<_>>();
    let [generated] = generated.as_slice() else {
        return Err(ProvisionalCompileError::InitializerIdentity {
            module: initializer.module.clone(),
            message: format!(
                "expected one generated initializer for cell {:?}, found {}",
                initializer.cell_name,
                generated.len()
            ),
        });
    };
    if generated != &initializer.emitted_name {
        return Err(ProvisionalCompileError::InitializerIdentity {
            module: initializer.module.clone(),
            message: format!(
                "frontend generated {generated:?} for cell {:?}, but Definition IR owns {:?}",
                initializer.cell_name, initializer.emitted_name
            ),
        });
    }
    Ok(())
}

#[cfg(test)]
mod tests;
