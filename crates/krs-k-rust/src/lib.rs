//! Versioned adapter to the native `k-rust` frontend.
//!
//! [`adapt_definition`] is the permanent structural boundary. The resulting
//! native source definition is prepared by [`prepare_definition`], an isolated
//! compatibility layer over the pinned frontend's public loader,
//! configuration expander, and graph resolver. The exact pin predates the
//! later upstream structured-preparation convenience API.
//!
//! [`compile_definition_provisional_oracle`] exists only as an explicitly
//! provisional M2 oracle. It parses no K source (and in particular never
//! parses emitted candidate `.k`); it uses the public configuration-expansion
//! and graph-resolution passes before isolating the unavoidable public-field
//! assembly in one function.

use std::{
    collections::{BTreeMap, BTreeSet},
    error::Error,
    fmt::{self, Write as _},
};

use k_rust::{
    builtin,
    definition::{
        self as native_definition, Attributes as NativeAttributes, FlatImport, FlatModule,
        ProductionItem as NativeItem, ResolvedDefinition, Sentence as NativeSentence,
        expand_configurations,
    },
    diagnostic::{Diagnostic as NativeDiagnostic, Severity as NativeSeverity},
    kast::{Label as NativeLabel, Sort as NativeSort, Term as NativeTerm},
    kompile,
    kore::{
        ast::{
            Definition as KoreDefinition, Pattern as KorePattern, Sentence as KoreSentence,
            Sort as KoreSort, Variable as KoreVariable, VariableKind as KoreVariableKind,
        },
        parser::parse_definition as parse_kore_definition,
        printer::Printer as KorePrinter,
    },
    outer::{LoadOptions as NativeLoadOptions, ResolvedSource, load_with_options},
};
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
pub use k_rust::outer::LoadedDefinition;

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
    source_revision: "0de7983f76f87ce93b91f5d3e994f0a2c3ff710c",
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

impl CapabilityAvailability {
    /// Returns whether the capability is available.
    #[must_use]
    pub const fn is_available(self) -> bool {
        matches!(self, Self::Available)
    }
}

const SUPPORTED_BACKENDS: &[Backend] = &[Backend::Llvm, Backend::Haskell];

/// Capabilities compiled into the pinned frontend and supplied by this adapter.
pub const FRONTEND_CAPABILITIES: FrontendCapabilities = FrontendCapabilities {
    backends: SUPPORTED_BACKENDS,
    z3_inference: CapabilityAvailability::Available,
    mpfr_folding: CapabilityAvailability::Unavailable(
        "the pinned k-rust dependency is built without mpfr-folding",
    ),
    structured_definition_preparation: CapabilityAvailability::Available,
};

/// Import policy of the provisional M2 preparation route.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PortablePreludePolicy {
    /// Resolve structured IR against the pinned native builtin closure.
    PinnedBuiltinClosure,
}

/// Prelude policy used by [`compile_definition_provisional_oracle`].
pub const PORTABLE_PRELUDE_POLICY: PortablePreludePolicy =
    PortablePreludePolicy::PinnedBuiltinClosure;

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
/// attributes retain a portable package-relative source name plus the exact
/// Definition IR source-map key consumed by diagnostic translation; a native
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

/// A native capability boundary retained for compatibility with the
/// provisional M2 oracle harness.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum CapabilityError {
    /// The pinned frontend has no direct upstream structured-preparation
    /// convenience API. The permanent path supplies [`prepare_definition`]
    /// instead and does not return this error.
    StructuredDefinitionPreparationUnavailable,
}

impl fmt::Display for CapabilityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::StructuredDefinitionPreparationUnavailable => formatter.write_str(
                "k-rust 0.3.0 has no direct structured Definition preparation convenience API",
            ),
        }
    }
}

impl Error for CapabilityError {}

/// Structural Definition-IR adaptation failure.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum AdapterError {
    /// A compatibility capability boundary was crossed.
    Capability(CapabilityError),
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
            Self::MissingReference { key, kind, target } => write!(
                formatter,
                "Definition IR {kind} reference {target:?} at {:?} is absent from the adapter index",
                key.as_str()
            ),
        }
    }
}

impl Error for AdapterError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Capability(error) => Some(error),
            Self::MissingSymbol { .. } | Self::MissingReference { .. } => None,
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
    /// Definition IR could not be represented by the schema-9 adapter.
    Adapter(AdapterError),
    /// The adapted source Definition cannot be prepared through a supported
    /// pinned-frontend API.
    Capability(CapabilityError),
    /// The pinned public preparation primitives rejected the native graph.
    Preparation(String),
    /// The ordered native compiler rejected the prepared graph.
    Compile {
        /// Native pipeline stage.
        stage: &'static str,
        /// Native pipeline message.
        message: String,
        /// Structured frontend diagnostics.
        diagnostics: Vec<FrontendDiagnostic>,
    },
    /// A produced KORE definition did not reparse under the exact pin.
    KoreReparse {
        /// Artifact which failed.
        artifact: &'static str,
        /// Parser message.
        message: String,
    },
}

impl fmt::Display for DefinitionCompileError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Adapter(error) => error.fmt(formatter),
            Self::Capability(error) => error.fmt(formatter),
            Self::Preparation(message) => write!(formatter, "native preparation failed: {message}"),
            Self::Compile { stage, message, .. } => {
                write!(
                    formatter,
                    "native frontend stage {stage:?} failed: {message}"
                )
            }
            Self::KoreReparse { artifact, message } => {
                write!(formatter, "pinned parser rejected {artifact}: {message}")
            }
        }
    }
}

impl Error for DefinitionCompileError {
    fn source(&self) -> Option<&(dyn Error + 'static)> {
        match self {
            Self::Adapter(error) => Some(error),
            Self::Capability(error) => Some(error),
            Self::Preparation(_) | Self::Compile { .. } | Self::KoreReparse { .. } => None,
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
                write!(
                    formatter,
                    "structured configuration expansion failed: {message}"
                )
            }
            Self::Resolution(message) => {
                write!(
                    formatter,
                    "expanded native definition resolution failed: {message}"
                )
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
    Adapter::new(ir).adapt(ir)
}

/// Prepare one structurally adapted definition through public pinned APIs.
///
/// This compatibility layer first lets the public
/// loader establish the bundled prelude, backend filtering, source-file set,
/// and graph invariants from a fixed empty bootstrap module. It then replaces
/// that module with the already-structured KRS modules, expands structured
/// configurations, and resolves the resulting graph. It never parses emitted
/// KRS `.k` source.
///
/// # Errors
///
/// Returns a stable message when the pinned loader, configuration expander, or
/// resolver rejects the graph.
pub fn prepare_definition(
    definition: NativeDefinition,
    backend: Backend,
) -> Result<LoadedDefinition, String> {
    const BOOTSTRAP_MODULE: &str = "KRS-STRUCTURED-BOOTSTRAP";
    const DEFAULT_CONFIGURATION_MODULE: &str = "DEFAULT-CONFIGURATION";
    let local_modules = definition
        .modules
        .iter()
        .map(|module| module.name.as_str())
        .collect::<BTreeSet<_>>();
    let bootstrap_imports = definition
        .modules
        .iter()
        .flat_map(|module| module.imports.iter())
        .filter(|import| !local_modules.contains(import.name.as_str()))
        .map(|import| import.name.as_str())
        .collect::<BTreeSet<_>>();
    let bootstrap_imports =
        bootstrap_imports
            .into_iter()
            .fold(String::new(), |mut source, name| {
                writeln!(source, "  imports {name}").expect("writing to String cannot fail");
                source
            });
    let bootstrap_source = format!("module {BOOTSTRAP_MODULE}\n{bootstrap_imports}endmodule\n");
    let prelude = builtin::embedded("prelude.md")
        .ok_or_else(|| "pinned compatibility prelude is unavailable".to_owned())?;
    let mut resolver = |_: &str, required: &str| {
        builtin::embedded(required).ok_or_else(|| format!("missing pinned source {required:?}"))
    };
    let excluded = match backend {
        Backend::Llvm => kompile::CompilationBackend::Llvm.excluded_module_attribute(),
        Backend::Haskell => kompile::CompilationBackend::Rust.excluded_module_attribute(),
    };
    let mut loaded = load_with_options(
        ResolvedSource::new("krs-structured-bootstrap.k", bootstrap_source),
        BOOTSTRAP_MODULE,
        &mut resolver,
        &NativeLoadOptions {
            implicit_sources: vec![prelude],
            excluded_module_attributes: vec![excluded.to_owned()],
            ..NativeLoadOptions::default()
        },
    )
    .map_err(|error| error.to_string())?;

    loaded.definition.modules.retain(|module| {
        module.name != BOOTSTRAP_MODULE && module.name != DEFAULT_CONFIGURATION_MODULE
    });
    for module in &mut loaded.definition.modules {
        module
            .imports
            .retain(|import| import.name != DEFAULT_CONFIGURATION_MODULE);
    }
    for module in &definition.modules {
        if loaded
            .definition
            .modules
            .iter()
            .any(|existing| existing.name == module.name)
        {
            return Err(format!(
                "structured module {:?} conflicts with a pinned prelude module",
                module.name
            ));
        }
    }
    loaded.definition.modules.extend(definition.modules);
    loaded.definition.main_module = definition.main_module;
    loaded.definition.attributes = definition.attributes;
    loaded.definition =
        expand_configurations(&loaded.definition).map_err(|error| error.to_string())?;
    loaded.resolved =
        ResolvedDefinition::resolve(&loaded.definition).map_err(|error| error.to_string())?;
    Ok(loaded)
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
    let adapted = adapt_definition(ir).map_err(DefinitionCompileError::Adapter)?;
    let loaded = prepare_definition(adapted.definition.clone(), options.backend)
        .map_err(DefinitionCompileError::Preparation)?;
    for initializer in &adapted.initializers {
        validate_initializer_identity(&loaded.definition, initializer)
            .map_err(|error| DefinitionCompileError::Preparation(error.to_string()))?;
    }
    let mut artifacts = compile_loaded_definition(&loaded, options).map_err(|error| {
        let authored_existential_keys = authored_existential_sentence_keys(ir);
        let diagnostics = error
            .diagnostics()
            .iter()
            .filter(|diagnostic| {
                diagnostic.code != "UnsupportedExistentialVariable"
                    || diagnostic
                        .source
                        .as_deref()
                        .and_then(native_source_map_key)
                        .is_none_or(|key| authored_existential_keys.contains(key))
            })
            .cloned()
            .collect();
        DefinitionCompileError::Compile {
            stage: error.stage(),
            message: error.message().to_owned(),
            diagnostics,
        }
    })?;
    artifacts.definition_kore =
        disambiguate_kore_variable_sorts(&artifacts.definition_kore, options.kore_width).map_err(
            |message| DefinitionCompileError::KoreReparse {
                artifact: "definition.kore",
                message,
            },
        )?;
    parse_kore_definition(&artifacts.definition_kore).map_err(|error| {
        DefinitionCompileError::KoreReparse {
            artifact: "definition.kore",
            message: error.to_string(),
        }
    })?;
    parse_kore_definition(&artifacts.syntax_definition_kore).map_err(|error| {
        DefinitionCompileError::KoreReparse {
            artifact: "syntaxDefinition.kore",
            message: error.to_string(),
        }
    })?;
    Ok(artifacts)
}

/// Repair the pinned frontend's sentence-local `_GenN` collision between
/// `ConcretizeCells` output and its later term-construction minimizer.
///
/// KORE identifies a variable by kind and name and requires one sort for that
/// identity. The pinned compiler can allocate the same `_GenN` name to two
/// independent terms of different sorts. Rename only the later sorted
/// identities, consistently across one sentence, and leave collision-free
/// output byte-for-byte untouched.
fn disambiguate_kore_variable_sorts(source: &str, width: usize) -> Result<String, String> {
    let mut definition = parse_kore_definition(source).map_err(|error| error.to_string())?;
    let mut repaired = 0_usize;
    for module in &mut definition.modules {
        for sentence in &mut module.sentences {
            repaired += disambiguate_kore_sentence(sentence);
        }
    }
    if repaired == 0 {
        return Ok(source.to_owned());
    }
    ensure_kore_variable_sorts_are_unique(&mut definition)?;
    let mut rendered = KorePrinter::pretty(width).print_definition(&definition);
    if !rendered.ends_with('\n') {
        rendered.push('\n');
    }
    Ok(rendered)
}

fn disambiguate_kore_sentence(sentence: &mut KoreSentence) -> usize {
    let mut sorts_by_name = BTreeMap::<(KoreVariableKind, String), BTreeSet<KoreSort>>::new();
    let mut used_names = BTreeSet::new();
    for pattern in kore_sentence_patterns_mut(sentence) {
        visit_kore_variables_mut(pattern, &mut |variable| {
            used_names.insert(variable.name.clone());
            sorts_by_name
                .entry((variable.kind, variable.name.clone()))
                .or_default()
                .insert(variable.sort.clone());
        });
    }

    let mut next = 0_usize;
    let mut renames = BTreeMap::<(KoreVariableKind, String, KoreSort), String>::new();
    for ((kind, name), sorts) in sorts_by_name {
        if sorts.len() < 2 {
            continue;
        }
        for sort in sorts.into_iter().skip(1) {
            let replacement = loop {
                let candidate = format!("KRSVar{next}");
                next += 1;
                if used_names.insert(candidate.clone()) {
                    break candidate;
                }
            };
            renames.insert((kind, name.clone(), sort), replacement);
        }
    }
    if renames.is_empty() {
        return 0;
    }
    for pattern in kore_sentence_patterns_mut(sentence) {
        visit_kore_variables_mut(pattern, &mut |variable| {
            if let Some(replacement) =
                renames.get(&(variable.kind, variable.name.clone(), variable.sort.clone()))
            {
                variable.name.clone_from(replacement);
            }
        });
    }
    renames.len()
}

fn ensure_kore_variable_sorts_are_unique(definition: &mut KoreDefinition) -> Result<(), String> {
    for module in &mut definition.modules {
        for sentence in &mut module.sentences {
            let mut sorts_by_name =
                BTreeMap::<(KoreVariableKind, String), BTreeSet<KoreSort>>::new();
            for pattern in kore_sentence_patterns_mut(sentence) {
                visit_kore_variables_mut(pattern, &mut |variable| {
                    sorts_by_name
                        .entry((variable.kind, variable.name.clone()))
                        .or_default()
                        .insert(variable.sort.clone());
                });
            }
            if let Some(((kind, name), sorts)) =
                sorts_by_name.into_iter().find(|(_, sorts)| sorts.len() > 1)
            {
                return Err(format!(
                    "KORE variable {kind:?} {name:?} still has multiple sorts: {sorts:?}"
                ));
            }
        }
    }
    Ok(())
}

fn kore_sentence_patterns_mut(sentence: &mut KoreSentence) -> Vec<&mut KorePattern> {
    match sentence {
        KoreSentence::Import { attributes, .. }
        | KoreSentence::SortDeclaration { attributes, .. }
        | KoreSentence::SymbolDeclaration { attributes, .. } => attributes.0.iter_mut().collect(),
        KoreSentence::AliasDeclaration {
            left,
            right,
            attributes,
            ..
        } => {
            let mut patterns = vec![left.as_mut(), right.as_mut()];
            patterns.extend(attributes.0.iter_mut());
            patterns
        }
        KoreSentence::Axiom {
            pattern,
            attributes,
            ..
        }
        | KoreSentence::Claim {
            pattern,
            attributes,
            ..
        } => {
            let mut patterns = vec![pattern.as_mut()];
            patterns.extend(attributes.0.iter_mut());
            patterns
        }
    }
}

fn visit_kore_variables_mut(
    pattern: &mut KorePattern,
    visitor: &mut impl FnMut(&mut KoreVariable),
) {
    match pattern {
        KorePattern::Variable(variable) => visitor(variable),
        KorePattern::Application { arguments, .. }
        | KorePattern::And { arguments, .. }
        | KorePattern::Or { arguments, .. }
        | KorePattern::AssociativeApplication { arguments, .. } => {
            for argument in arguments {
                visit_kore_variables_mut(argument, visitor);
            }
        }
        KorePattern::Not { argument, .. }
        | KorePattern::Next { argument, .. }
        | KorePattern::Ceil { argument, .. }
        | KorePattern::Floor { argument, .. } => visit_kore_variables_mut(argument, visitor),
        KorePattern::Implies { left, right, .. }
        | KorePattern::Iff { left, right, .. }
        | KorePattern::Rewrites { left, right, .. }
        | KorePattern::Equals { left, right, .. }
        | KorePattern::In { left, right, .. } => {
            visit_kore_variables_mut(left, visitor);
            visit_kore_variables_mut(right, visitor);
        }
        KorePattern::Exists { variable, body, .. }
        | KorePattern::Forall { variable, body, .. }
        | KorePattern::Mu { variable, body }
        | KorePattern::Nu { variable, body } => {
            visitor(variable);
            visit_kore_variables_mut(body, visitor);
        }
        KorePattern::String(_)
        | KorePattern::Top { .. }
        | KorePattern::Bottom { .. }
        | KorePattern::DomainValue { .. } => {}
    }
}

fn authored_existential_sentence_keys(ir: &DefinitionIr) -> BTreeSet<&str> {
    ir.modules()
        .iter()
        .flat_map(krs_ir::DefinitionModule::sentences)
        .filter_map(|sentence| {
            let DefinitionSentence::Rule(rule) = sentence else {
                return None;
            };
            rule.claim()
                .is_some_and(|claim| !claim.existentials().is_empty())
                .then(|| rule.origin().key().as_str())
        })
        .collect()
}

fn native_source_map_key(source: &str) -> Option<&str> {
    source
        .rsplit_once("#krs-source-map=")
        .map(|(_, key)| key)
        .filter(|key| !key.is_empty())
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
/// This route resolves builtin imports against the same pinned native closure
/// as the permanent structured compiler.
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
    let loaded = prepare_provisional_oracle(&adapted, options.backend)?;
    let artifacts =
        compile_loaded_definition(&loaded, options).map_err(ProvisionalCompileError::Compile)?;
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
        Backend::Haskell => kompile::CompilationBackend::Rust,
    };
    let artifacts = kompile::compile_loaded_definition(
        loaded,
        kompile::CompileOptions {
            backend,
            kore_width: options.kore_width,
            default_claims_to_all_path: false,
            hook_namespaces: None,
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
    groups: BTreeMap<ProductionGroupId, String>,
    context_aliases: BTreeMap<StableItemId, String>,
    cells: BTreeMap<SymbolId, String>,
    initializer_variables: BTreeMap<SemanticId, String>,
    context_here: Option<SemanticId>,
    origins: Vec<OriginMapping>,
    initializers: Vec<InitializerIdentity>,
}

#[derive(Clone, Copy, Eq, PartialEq)]
enum TermContext {
    Normal,
    ConfigurationInitializer,
    ContextAlias,
}

impl Adapter {
    fn new(ir: &DefinitionIr) -> Self {
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
                    DefinitionSentence::Configuration(sentence) if sentence.cell().is_some() => {
                        let cell = sentence.cell().expect("legacy configuration cell");
                        let initializer = sentence
                            .initializer()
                            .expect("legacy configuration initializer");
                        symbols.insert(
                            cell.symbol().id().clone(),
                            cell.symbol().emitted_name().to_owned(),
                        );
                        cells.insert(
                            cell.symbol().id().clone(),
                            cell.symbol().emitted_name().to_owned(),
                        );
                        symbols.insert(
                            initializer.symbol().id().clone(),
                            initializer.symbol().emitted_name().to_owned(),
                        );
                    }
                    DefinitionSentence::Configuration(sentence) => {
                        let configuration = sentence
                            .as_fixed()
                            .expect("non-legacy configuration is fixed");
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
        self.map_origin(module.origin(), &module_name, None, NativeNodeRole::Module);
        let mut local_sentences = Vec::with_capacity(module.sentences().len());
        for sentence in module.sentences() {
            let sentence_index = local_sentences.len();
            let native = self.sentence(sentence, &module_name, sentence_index)?;
            local_sentences.push(native);
        }
        let mut imports = module
            .imports()
            .iter()
            .map(|import| import.as_str().to_owned())
            .collect::<BTreeSet<_>>();
        imports.extend(module_builtin_imports(module));
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
            self.map_origin(
                attribute.origin(),
                module,
                Some(sentence_index),
                NativeNodeRole::ProductionAttribute(index),
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
                self.map_origin(
                    item.origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ProductionItem(u32::try_from(index).unwrap_or(u32::MAX)),
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
        Ok(NativeSentence::Production {
            label: Some(NativeLabel::new(sentence.symbol().emitted_name())),
            parameters: Vec::new(),
            sort: self.sort(sentence.result_sort(), sentence.origin())?,
            items,
            attributes,
        })
    }

    #[allow(clippy::too_many_arguments, clippy::too_many_lines)]
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
                    self.map_origin(
                        selected.origin(),
                        module,
                        Some(sentence_index),
                        NativeNodeRole::StrictnessField(u32::try_from(index).unwrap_or(u32::MAX)),
                    );
                }
                self.map_origin(
                    result_sort.origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::StrictnessResult,
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
                    self.map_origin(
                        using.origin(),
                        module,
                        Some(sentence_index),
                        NativeNodeRole::StrictnessContextAlias,
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
        sentence: &ConfigurationSentence,
        module: &str,
        sentence_index: usize,
    ) -> Result<NativeSentence, AdapterError> {
        self.initializer_variables.clear();
        let body =
            if let (Some(cell), Some(initializer)) = (sentence.cell(), sentence.initializer()) {
                for variable in initializer.variables() {
                    self.initializer_variables
                        .insert(variable.id().clone(), variable.id().as_str().to_owned());
                }
                self.map_origin(
                    cell.origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ConfigurationCell,
                );
                self.map_origin(
                    initializer.origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ConfigurationInitializer,
                );
                let cell_name = cell.symbol().emitted_name().to_owned();
                let contents = self.term(
                    initializer.body(),
                    module,
                    sentence_index,
                    Vec::new(),
                    TermContext::ConfigurationInitializer,
                    None,
                )?;
                self.initializers.push(InitializerIdentity {
                    module: module.to_owned(),
                    cell_name: cell_name.clone(),
                    emitted_name: initializer.symbol().emitted_name().to_owned(),
                });
                native_config_cell(
                    &cell_name,
                    NativeTerm::apply("#cellPropertyListTerminator", Vec::new()),
                    contents,
                )
            } else {
                let configuration = sentence
                    .as_fixed()
                    .expect("configuration is legacy or fixed");
                for variable in configuration.variables() {
                    self.initializer_variables
                        .insert(variable.id().clone(), variable.external_name().to_owned());
                    self.map_origin(
                        variable.origin(),
                        module,
                        Some(sentence_index),
                        NativeNodeRole::ConfigurationInitializer,
                    );
                }
                self.map_origin(
                    configuration.initializer_origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ConfigurationInitializer,
                );
                self.fixed_configuration(configuration, module, sentence_index)?
            };
        self.initializer_variables.clear();
        Ok(NativeSentence::Configuration {
            body,
            ensures: truth(),
            attributes: attributes_for_origin(sentence.origin()),
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
                self.map_origin(
                    origin,
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ConfigurationCell,
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
        self.map_origin(
            cell.origin(),
            module,
            Some(sentence_index),
            NativeNodeRole::ConfigurationCell,
        );
        self.map_origin(
            initializer.origin(),
            module,
            Some(sentence_index),
            NativeNodeRole::ConfigurationInitializer,
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
        self.map_origin(
            sentence.name_origin(),
            module,
            Some(sentence_index),
            NativeNodeRole::ContextAliasName,
        );
        self.map_origin(
            sentence.here_origin(),
            module,
            Some(sentence_index),
            NativeNodeRole::ContextAliasHere,
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
                self.map_origin(
                    condition.origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::Requires,
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
                    self.map_origin(
                        condition.origin(),
                        module,
                        Some(sentence_index),
                        NativeNodeRole::Ensures,
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
            self.map_origin(
                claim.modality_origin(),
                module,
                Some(sentence_index),
                NativeNodeRole::ClaimModality,
            );
            attributes.insert(claim_modality_attribute(claim.modality()), json!(""));
            if let Some(origin) = claim.circularity_origin() {
                self.map_origin(
                    origin,
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ClaimCircularity,
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
            (binder.origin(), NativeNodeRole::ClaimBinder(index)),
            (binder.name_origin(), NativeNodeRole::ClaimBinderName(index)),
            (binder.sort_origin(), NativeNodeRole::ClaimBinderSort(index)),
        ] {
            self.map_origin(origin, module, Some(sentence_index), role);
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
                self.map_origin(
                    clause.origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ConfigurationRuleCell(index),
                );
                if let CellContentFrame::KSequenceTail { origin, .. }
                | CellContentFrame::MapRemainder { origin, .. } = clause.frame()
                {
                    self.map_origin(
                        origin,
                        module,
                        Some(sentence_index),
                        NativeNodeRole::ConfigurationRuleFrame(index),
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
                self.map_origin(
                    cell.origin(),
                    module,
                    Some(sentence_index),
                    NativeNodeRole::ContextAliasCell(index),
                );
                if let CellContentFrame::KSequenceTail { origin, .. }
                | CellContentFrame::MapRemainder { origin, .. } = cell.frame()
                {
                    self.map_origin(
                        origin,
                        module,
                        Some(sentence_index),
                        NativeNodeRole::ContextAliasFrame(index),
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
        self.map_origin(
            term.origin(),
            module,
            Some(sentence_index),
            NativeNodeRole::Term(path.clone()),
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
                target: format!("{operation:?}/{}", arguments.len()),
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
                    target: format!("{operation:?}/{}", arguments.len()),
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
            (SetOperation::Contains, 2) => "Set:in",
            _ => {
                return Err(AdapterError::MissingReference {
                    key: origin.key().clone(),
                    kind: "Set operation arity",
                    target: format!("{operation:?}/{}", arguments.len()),
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
            DefinitionSortRef::Builtin(BuiltinSort::KSequence) => "K",
            DefinitionSortRef::Builtin(BuiltinSort::Int) => "Int",
            DefinitionSortRef::Builtin(BuiltinSort::Bool) => "Bool",
            DefinitionSortRef::Builtin(BuiltinSort::Map) => "Map",
            DefinitionSortRef::Builtin(BuiltinSort::Id) => "Id",
            DefinitionSortRef::Builtin(BuiltinSort::Bytes) => "Bytes",
            DefinitionSortRef::Builtin(BuiltinSort::List) => "List",
            DefinitionSortRef::Builtin(BuiltinSort::Set) => "Set",
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
                target: format!("{alias:?}"),
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
                if let Some(cell) = sentence.cell() {
                    collect_builtin_sort(cell.content_sort(), &mut sorts);
                }
                if let Some(initializer) = sentence.initializer() {
                    for variable in initializer.variables() {
                        collect_builtin_sort(variable.sort(), &mut sorts);
                    }
                    collect_term_builtins(initializer.body(), &mut sorts);
                }
                if let Some(configuration) = sentence.as_fixed() {
                    collect_fixed_configuration_builtins(configuration, &mut sorts);
                }
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
        .filter_map(|sort| match sort {
            BuiltinSort::KSequence => None,
            BuiltinSort::Int => Some("INT".to_owned()),
            BuiltinSort::Bool => Some("BOOL".to_owned()),
            BuiltinSort::Map => Some("MAP".to_owned()),
            BuiltinSort::Id => Some("ID-SYNTAX".to_owned()),
            BuiltinSort::Bytes => Some("BYTES".to_owned()),
            BuiltinSort::List => Some("LIST".to_owned()),
            BuiltinSort::Set => Some("SET".to_owned()),
        })
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
                // K's source claim concretizer allocates its internal counter
                // after authored existential names. Keep the compatibility
                // variable in that same deterministic ordering class.
                name: format!("?KRSCOUNTER{sentence_index}"),
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
        format!("?{}", variable.as_str().to_ascii_uppercase())
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
    match operation {
        BuiltinOperation::IntAdd => "_+Int_",
        BuiltinOperation::IntSub => "_-Int_",
        BuiltinOperation::IntMul => "_*Int_",
        BuiltinOperation::IntTDiv => "_/Int_",
        BuiltinOperation::IntMod => "_modInt_",
        BuiltinOperation::IntPowMod => "_^%Int__",
        BuiltinOperation::IntLog2 => "log2Int(_)_INT-COMMON_Int_Int",
        BuiltinOperation::IntShiftRight => "_>>Int_",
        BuiltinOperation::IntShiftLeft => "_<<Int_",
        BuiltinOperation::IntBitAnd => "_&Int_",
        BuiltinOperation::IntBitXor => "_xorInt_",
        BuiltinOperation::IntBitOr => "_|Int_",
        BuiltinOperation::IntGreaterEqual => "_>=Int_",
        BuiltinOperation::IntGreater => "_>Int_",
        BuiltinOperation::IntLessEqual => "_<=Int_",
        BuiltinOperation::IntLess => "_<Int_",
        BuiltinOperation::IntEqual => "_==Int_",
        BuiltinOperation::IntNotEqual => "_=/=Int_",
        BuiltinOperation::BoolNot => "notBool_",
        BuiltinOperation::BoolEqual => "_==Bool_",
        BuiltinOperation::BoolNotEqual => "_=/=Bool_",
        BuiltinOperation::BoolAnd => "_andBool_",
        BuiltinOperation::BoolOr => "_orBool_",
        BuiltinOperation::BytesLength => "lengthBytes(_)_BYTES-HOOKED_Int_Bytes",
        BuiltinOperation::BytesGet => "_[_]_BYTES-HOOKED_Int_Bytes_Int",
        BuiltinOperation::BytesEmpty => ".Bytes_BYTES-HOOKED_Bytes",
        BuiltinOperation::BytesUpdate => "_[_<-_]_BYTES-HOOKED_Bytes_Bytes_Int_Int",
        BuiltinOperation::BytesPadRight => "padRightBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int",
        BuiltinOperation::BytesSubstring => "substrBytes(_,_,_)_BYTES-HOOKED_Bytes_Bytes_Int_Int",
    }
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
        attributes.insert(
            native_definition::SOURCE_ATTRIBUTE,
            json!(format!("{source}#krs-source-map={}", origin.key().as_str())),
        );
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
    adapted: &AdaptedDefinition,
    backend: Backend,
) -> Result<LoadedDefinition, ProvisionalCompileError> {
    let loaded = prepare_definition(adapted.definition.clone(), backend)
        .map_err(ProvisionalCompileError::Configuration)?;
    for initializer in &adapted.initializers {
        validate_initializer_identity(&loaded.definition, initializer)?;
    }
    Ok(loaded)
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
