//! Versioned adapter to the native `k-rust` frontend.
//!
//! [`compile_definition`] is the route from Definition IR to compiled artifacts.
//! It adapts the IR to a native source definition, prepares it through the pinned frontend's structured loader, compiles it, reparses both KORE definitions, and joins sentence provenance.
//! The route does not parse emitted candidate `.k` source.

mod adapter;
mod error;
mod provenance;

use std::collections::BTreeMap;

use k_rust::{
    builtin,
    definition::{CheckMode as NativeCheckMode, Sentence as NativeSentence},
    kast::Sort as NativeSort,
    kompile,
    kore::parser::parse_definition as parse_kore_definition,
    outer::{LoadOptions as NativeLoadOptions, load_structured},
};
use krs_ir::measure::Timings;
use krs_ir_levels::DefinitionIr;

use error::resolve_diagnostic_keys;
use provenance::join_sentence_provenance;

pub use k_rust::definition::Definition as NativeDefinition;
pub use k_rust::kompile::EmittedSentenceProvenance;
pub use k_rust::outer::LoadedDefinition;
pub use k_rust::provenance::{GeneratingPass, InputAddress, InputSentenceKind, InputSpace};
pub use k_rust::timings::PhaseTimings as NativePhaseTimings;

pub use adapter::{
    AdaptedDefinition, AdapterError, NativeNodePlace, OriginMapping, SentenceNodeRole,
    adapt_definition, adapt_definition_for,
};
pub use error::{
    CompileError, DefinitionCompileError, DiagnosticSeverity, FrontendDiagnostic, PreparationError,
    SourceLocation, diagnostic_source_map_key,
};
pub use provenance::{Author, EmittedProvenance, ProvenanceError, SentenceProvenance};

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
    source_revision: "195a77180add343b1ba2313dc20ae230bb7d3350",
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

/// A route that runs a KRS definition, for the backend capability table (V8).
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum Route {
    /// The in-process k-rust backend on symbolic KORE (`krs build --backend haskell`, `krs prove`).
    NativeRust,
    /// The in-process k-rust frontend emitting LLVM KORE (`krs build --backend llvm`).
    NativeLlvm,
    /// Java K's LLVM backend on the emitted `.k` (reference gates).
    JavaLlvmReference,
    /// Java K's Haskell backend on the emitted `.k` (reference proofs).
    JavaHaskellReference,
    /// The browser lesson worker.
    Browser,
}

impl Route {
    /// Every route, in table order.
    pub const ALL: [Self; 5] = [
        Self::NativeRust,
        Self::NativeLlvm,
        Self::JavaLlvmReference,
        Self::JavaHaskellReference,
        Self::Browser,
    ];

    /// The stable route name.
    #[must_use]
    pub const fn name(self) -> &'static str {
        match self {
            Self::NativeRust => "native-rust",
            Self::NativeLlvm => "native-llvm",
            Self::JavaLlvmReference => "java-llvm-reference",
            Self::JavaHaskellReference => "java-haskell-reference",
            Self::Browser => "browser",
        }
    }

    /// The route with the given stable name.
    #[must_use]
    pub fn from_name(name: &str) -> Option<Self> {
        Self::ALL.into_iter().find(|route| route.name() == name)
    }

    /// The native route that compiles for `backend`.
    #[must_use]
    pub const fn native(backend: Backend) -> Self {
        match backend {
            Backend::Llvm => Self::NativeLlvm,
            Backend::Haskell => Self::NativeRust,
        }
    }
}

/// One row of the backend capability table: a feature and the routes that lack it.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub struct RouteCapability {
    /// Stable feature name, as `krs_compiler::capability::CapabilityFeature::name` spells it.
    pub feature: &'static str,
    /// Routes that cannot run the feature.
    pub unavailable_on: &'static [Route],
    /// Why, and what to run instead; the refusal message ends with it.
    pub reason: &'static str,
    /// Where the limitation is recorded.
    pub evidence: &'static str,
}

/// The backend capability table, one row per feature (append-only).
pub const ROUTE_CAPABILITIES: &[RouteCapability] = &[
    RouteCapability {
        feature: "AnywhereRule",
        unavailable_on: &[Route::JavaHaskellReference],
        reason: "K 7.1.337's Haskell backend rejects them (and --allow-anywhere-haskell would drop them); run this on the LLVM or k-rust route",
        evidence: "Java kompile --backend haskell refuses an `anywhere` rule unless --allow-anywhere-haskell, which drops it; k-rust implements anywhere rules (docs/compatibility.md)",
    },
    RouteCapability {
        feature: "GroundFloatFolding",
        unavailable_on: &[Route::NativeRust, Route::NativeLlvm, Route::Browser],
        reason: "the pinned native frontend folds ground Float applications and is built without MPFR; bind a variable or write the folded literal",
        evidence: "k-rust 195a7718 kompile/passes/constant_folding.rs refuses FLOAT.* folding without the mpfr-folding feature, which KRS does not enable (FRONTEND_CAPABILITIES.mpfr_folding)",
    },
    RouteCapability {
        feature: "FloatPrecisionBeyondBinary64",
        unavailable_on: &[Route::NativeRust, Route::NativeLlvm, Route::Browser],
        reason: "k-rust evaluates Float only as binary32 (p24x8, f32) and binary64 (p53x11, f64); run this on Java K's LLVM backend",
        evidence: "k-rust 195a7718 k-rust-backend builtin/float.rs rejects other precisions and exponent ranges",
    },
    RouteCapability {
        feature: "ConsoleIO",
        unavailable_on: &[Route::Browser],
        reason: "the browser route has no standard input or output; run it with `krs run` or Java K's krun",
        evidence: "the browser lesson runtime executes requests through the k-rust backend API, which performs no host IO (k-rust 195a7718 docs/compatibility.md: RPC does not perform host IO)",
    },
];

/// Whether `route` can run `feature`; a feature without a row is available everywhere.
#[must_use]
pub fn route_capability(feature: &str, route: Route) -> CapabilityAvailability {
    ROUTE_CAPABILITIES
        .iter()
        .find(|row| row.feature == feature && row.unavailable_on.contains(&route))
        .map_or(CapabilityAvailability::Available, |row| {
            CapabilityAvailability::Unavailable(row.reason)
        })
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
            error.resolve_raw_parse_error(ir);
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
        frontend_definition: loaded.into_definition(),
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
            check_mode: if loaded.definition().modules.iter().any(|module| {
                module
                    .local_sentences
                    .iter()
                    .any(|sentence| matches!(**sentence, NativeSentence::Claim { .. }))
            }) {
                NativeCheckMode::Proof {
                    definition_module: loaded.definition().main_module.clone(),
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

#[cfg(test)]
mod test_fixtures;
#[cfg(test)]
mod tests;
