//! Mutant validation: kink-patch application followed by k-rust compilation.
//!
//! A mutant is compiled from the relinked loaded definition (`Mutant::to_loaded`),
//! not re-loaded: a loaded definition cannot be fed back through `load_structured`.
//! A KRS route that binds a pre-load definition with the embedded prelude waits
//! for the Z3-free structured compile (KRS-owned `z3-free-structured-compile`):
//! without Z3 the prelude does not load.

use std::{collections::BTreeMap, fmt, sync::OnceLock};

use k_rust::{
    definition::Definition,
    kompile::{CompileError, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition},
    outer::{LoadError, LoadedDefinition},
};
use kink_patch::{Baseline, Patch, PatchFailure, SentenceOrigin, SentenceRef, apply};

/// Typed failure to compile the native baseline. No staged output is published.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum NativeFailure {
    Compilation { stage: &'static str, detail: String },
}

impl fmt::Display for NativeFailure {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Compilation { stage, detail } => {
                write!(
                    formatter,
                    "native compilation stage {stage:?} failed: {detail}"
                )
            }
        }
    }
}

impl std::error::Error for NativeFailure {}

/// An immutable loaded baseline and the compile options every side uses.
///
/// It also holds the memoised result of [`NativeValidator::compile_baseline`]. A clone
/// carries the result its source already holds, which is the compile of the same
/// baseline under the same options.
#[derive(Clone, Debug)]
pub struct NativeValidator {
    baseline: Baseline,
    options: CompileOptions,
    compiled_baseline: OnceLock<Result<ValidatedDefinition, NativeFailure>>,
}

impl NativeValidator {
    /// Captures `baseline`; its caller owns prelude policy.
    pub const fn bind(baseline: Baseline, options: CompileOptions) -> Self {
        Self {
            baseline,
            options,
            compiled_baseline: OnceLock::new(),
        }
    }

    pub const fn baseline(&self) -> &Baseline {
        &self.baseline
    }

    /// Compiles the unpatched baseline, once per validator.
    ///
    /// The first call compiles; every later call, on this validator or on a clone made
    /// after it, returns a clone of that result, success or failure. The memo has no key
    /// of its own because the validator is the key: its baseline and compile options are
    /// fixed at [`NativeValidator::bind`] and never change. Returning the memo instead of
    /// compiling again rests on k-rust compile determinism (the same loaded definition
    /// under the same options compiles to the same artifacts), a premise replay already
    /// takes. Mutant compiles ([`NativeValidator::validate`]) are never memoised.
    pub fn compile_baseline(&self) -> Result<ValidatedDefinition, NativeFailure> {
        self.compiled_baseline
            .get_or_init(|| self.compile_baseline_uncached())
            .clone()
    }

    fn compile_baseline_uncached(&self) -> Result<ValidatedDefinition, NativeFailure> {
        let loaded = self.baseline.loaded();
        let artifacts = self
            .compile(loaded)
            .map_err(|error| NativeFailure::Compilation {
                stage: error.stage,
                detail: error
                    .diagnostics
                    .iter()
                    .fold(error.message, |detail, diagnostic| {
                        format!("{detail}; {}", diagnostic.message)
                    }),
            })?;
        Ok(ValidatedDefinition {
            definition: loaded.definition().clone(),
            artifacts,
            options: self.options.clone(),
            origins: None,
        })
    }

    /// Applies `patch` to the baseline and compiles the mutant.
    ///
    /// Nothing escapes on failure: a rejection holds only diagnostics, and a
    /// patched definition is published only inside a [`ValidatedDefinition`].
    pub fn validate(&self, patch: &Patch) -> Result<ValidatedDefinition, MutantRejection> {
        let mutant = apply(&self.baseline, patch).map_err(MutantRejection::Patch)?;
        let loaded = mutant
            .to_loaded(&self.baseline)
            .map_err(MutantRejection::Relink)?;
        let artifacts = self
            .compile(&loaded)
            .map_err(MutantRejection::Compilation)?;
        Ok(ValidatedDefinition {
            definition: loaded.into_definition(),
            artifacts,
            options: self.options.clone(),
            origins: Some(mutant.origins().clone()),
        })
    }

    fn compile(&self, loaded: &LoadedDefinition) -> Result<CompiledKoreArtifacts, CompileError> {
        compile_loaded_definition(loaded, self.options.clone())
    }
}

/// Why a patch did not yield a compiled mutant. It carries no definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MutantRejection {
    /// kink-patch rejected the patch; nothing was compiled.
    Patch(PatchFailure),
    /// k-rust rejected the patched definition; the error holds its stage
    /// and diagnostics only.
    Compilation(CompileError),
    /// k-rust refused to rebuild the patched definition at the loaded
    /// stage (`LoadedDefinition::with_definition`); nothing was compiled.
    Relink(LoadError),
}

impl fmt::Display for MutantRejection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Patch(failure) => write!(formatter, "patch rejected: {failure}"),
            Self::Compilation(error) => error.fmt(formatter),
            Self::Relink(error) => write!(formatter, "relink rejected: {error}"),
        }
    }
}

impl std::error::Error for MutantRejection {}

/// A compiled baseline or mutant. It is only built after compilation succeeded.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct ValidatedDefinition {
    definition: Definition,
    artifacts: CompiledKoreArtifacts,
    options: CompileOptions,
    origins: Option<BTreeMap<SentenceRef, SentenceOrigin>>,
}

impl ValidatedDefinition {
    /// Execution-relevant identity of the four compiled KORE fields.
    pub fn kore_sha256(&self) -> kink_patch::Sha256Digest {
        let value = serde_json::json!({
            "definition": self.artifacts.definition_kore,
            "macros": self.artifacts.macros_kore,
            "rewrite_order": self.artifacts.execution_rewrite_order,
            "syntax": self.artifacts.syntax_definition_kore,
        });
        kink_patch::payload_digest(
            kink_patch::COMPILED_KORE_DOMAIN,
            kink_patch::canonical_json(&value).as_bytes(),
        )
    }

    /// The loaded source definition that was compiled.
    pub const fn definition(&self) -> &Definition {
        &self.definition
    }

    pub const fn artifacts(&self) -> &CompiledKoreArtifacts {
        &self.artifacts
    }

    /// Exact backend, KORE width, claims mode, and hook namespace profile used for lowering.
    pub const fn compile_options(&self) -> &CompileOptions {
        &self.options
    }

    /// For a mutant, where each of its sentences came from; `None` for the baseline.
    pub const fn origins(&self) -> Option<&BTreeMap<SentenceRef, SentenceOrigin>> {
        self.origins.as_ref()
    }
}
