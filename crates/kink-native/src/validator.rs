//! Mutant validation: kink-patch application followed by k-rust compilation.
//!
//! A mutant is compiled from the relinked loaded definition (`Mutant::to_loaded`),
//! not re-loaded: a loaded definition cannot be fed back through `load_structured`.
//! A KRS route that binds a pre-load definition with the embedded prelude waits
//! for the Z3-free structured compile (KRS-owned `z3-free-structured-compile`):
//! without Z3 the prelude does not load.

use std::{collections::BTreeMap, fmt};

use k_rust::{
    definition::{AttributeKey, Definition, Sentence},
    kompile::{CompileError, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition},
    outer::LoadedDefinition,
};
use kink_patch::{Baseline, Patch, PatchFailure, SentenceOrigin, SentenceRef, apply};

use crate::NativeFailure;
use crate::observation::{
    DomainEventSpec, InstalledObservationManifest, ObservationFailure, RuleObservationSpec,
};

/// An immutable loaded baseline and the compile options every side uses.
#[derive(Clone, Debug)]
pub struct NativeValidator {
    baseline: Baseline,
    options: CompileOptions,
}

impl NativeValidator {
    /// Captures `baseline`; its caller owns prelude policy.
    pub const fn bind(baseline: Baseline, options: CompileOptions) -> Self {
        Self { baseline, options }
    }

    pub const fn baseline(&self) -> &Baseline {
        &self.baseline
    }

    /// Compiles the unpatched baseline.
    pub fn compile_baseline(&self) -> Result<ValidatedDefinition, NativeFailure> {
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
            definition: loaded.definition.clone(),
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
        let loaded = mutant.to_loaded(&self.baseline);
        let artifacts = self
            .compile(&loaded)
            .map_err(MutantRejection::Compilation)?;
        Ok(ValidatedDefinition {
            definition: loaded.definition,
            artifacts,
            options: self.options.clone(),
            origins: Some(mutant.origins().clone()),
        })
    }

    /// Installs `rules` for one compiled side, resolving each label to that side's
    /// `UNIQUE_ID`.
    ///
    /// A label must name an authored baseline sentence. On a mutant side, a label without
    /// a compiled rule is left out of the manifest only when the patch deleted that
    /// baseline sentence; any other unresolved label is a failure, so a mutant can never
    /// escape observation by losing or changing its label.
    pub fn observation_manifest(
        &self,
        side: &ValidatedDefinition,
        rules: &[ObservedRule],
    ) -> Result<InstalledObservationManifest, ManifestFailure> {
        let mut specs = Vec::with_capacity(rules.len());
        for rule in rules {
            let at = self
                .baseline
                .authored_sentences()
                .find(|(_, sentence)| {
                    sentence.attributes().string(AttributeKey::Label) == Some(rule.label.as_str())
                })
                .map(|(at, _)| at)
                .ok_or_else(|| ManifestFailure::UnknownLabel(rule.label.clone()))?;
            let identity = match side.rule_identity(&rule.label) {
                Ok(identity) => identity,
                Err(IdentityError::Missing)
                    if side.origins().is_some_and(|origins| {
                        !origins
                            .values()
                            .any(|origin| *origin == SentenceOrigin::Baseline(at.clone()))
                    }) =>
                {
                    continue;
                }
                Err(error) => {
                    return Err(ManifestFailure::Identity {
                        label: rule.label.clone(),
                        error,
                    });
                }
            };
            specs.push(RuleObservationSpec {
                label: rule.label.clone(),
                backend_rule_identity: identity.to_owned(),
                emit_rule_applied: rule.emit_rule_applied,
                domain_events: rule.domain_events.clone(),
            });
        }
        InstalledObservationManifest::install(specs).map_err(ManifestFailure::Installation)
    }

    fn compile(&self, loaded: &LoadedDefinition) -> Result<CompiledKoreArtifacts, CompileError> {
        compile_loaded_definition(loaded, self.options.clone())
    }
}

/// One rule to observe, selected by its module-qualified label on every compiled side.
#[derive(Clone, Debug, PartialEq)]
pub struct ObservedRule {
    pub label: String,
    pub emit_rule_applied: bool,
    pub domain_events: Vec<DomainEventSpec>,
}

/// Why an observation manifest cannot be installed for a compiled side.
#[derive(Clone, Debug, PartialEq)]
pub enum ManifestFailure {
    /// No authored baseline sentence has the label: a declaration error.
    UnknownLabel(String),
    /// The label does not resolve to one compiled rule on this side, and the patch did
    /// not delete its baseline sentence.
    Identity {
        label: String,
        error: IdentityError,
    },
    Installation(ObservationFailure),
}

/// Why a patch did not yield a compiled mutant. It carries no definition.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum MutantRejection {
    /// kink-patch rejected the patch; nothing was compiled.
    Patch(PatchFailure),
    /// k-rust rejected the patched definition; the error holds its stage
    /// and diagnostics only.
    Compilation(CompileError),
}

impl fmt::Display for MutantRejection {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Patch(failure) => write!(formatter, "patch rejected: {failure}"),
            Self::Compilation(error) => error.fmt(formatter),
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

    /// The `UNIQUE_ID` of the rule labelled `label` (module-qualified) in the
    /// compiled execution definition.
    ///
    /// `UNIQUE_ID` is content-derived, so a mutated rule has a different one
    /// on each compiled side; resolve it per side, never across sides.
    pub fn rule_identity(&self, label: &str) -> Result<&str, IdentityError> {
        let mut identities = self
            .artifacts
            .execution_definition
            .modules
            .iter()
            .flat_map(|module| module.local_sentences.iter())
            .filter(|sentence| {
                matches!(***sentence, Sentence::Rule { .. })
                    && sentence.attributes().string(AttributeKey::Label) == Some(label)
            })
            .map(|sentence| sentence.attributes().string(AttributeKey::UniqueId));
        let first = identities
            .next()
            .ok_or(IdentityError::Missing)?
            .ok_or(IdentityError::Missing)?;
        if identities.any(|other| other != Some(first)) {
            return Err(IdentityError::Ambiguous);
        }
        Ok(first)
    }
}

/// Why a rule label does not resolve to one compiled identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentityError {
    /// No compiled rule carries the label, or it has no `UNIQUE_ID`.
    Missing,
    /// Compiled rules with the label carry different `UNIQUE_ID`s.
    Ambiguous,
}

impl fmt::Display for IdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Missing => "no compiled rule identity for the label",
            Self::Ambiguous => "the label names several compiled rule identities",
        })
    }
}

impl std::error::Error for IdentityError {}
