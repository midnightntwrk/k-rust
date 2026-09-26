//! Mutant validation: kink-patch application followed by k-rust compilation.
//!
//! A mutant is compiled from the relinked loaded definition (`Mutant::to_loaded`),
//! not re-loaded: a loaded definition cannot be fed back through `load_structured`.
//! A KRS route that binds a pre-load definition with the embedded prelude waits
//! for the Z3-free structured compile (KRS-owned `z3-free-structured-compile`):
//! without Z3 the prelude does not load.

use std::{collections::BTreeMap, fmt};

use k_rust::{
    backend::{Backend, BackendOptions, CompiledRuleKind},
    definition::{AttributeKey, Definition, Location, Sentence},
    kompile::{CompileError, CompileOptions, CompiledKoreArtifacts, compile_loaded_definition},
    outer::LoadedDefinition,
    provenance::InputSpace,
};
use kink_patch::{Baseline, Patch, PatchFailure, SentenceOrigin, SentenceRef, apply};

use crate::observation::{
    AuthorObservation, DomainEventSpec, InstalledObservationManifest, ObservationFailure,
    RuleObservationSpec,
};

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

    /// Installs `rules` for one compiled side, resolving each written baseline
    /// position to that side's `UNIQUE_ID`.
    ///
    /// A position must name an authored baseline rule. On a mutant side, a position without
    /// a compiled rule is left out only when the patch deleted that baseline sentence;
    /// any other unresolved position is a failure.
    pub fn observation_manifest(
        &self,
        side: &ValidatedDefinition,
        rules: &[ObservedRule],
    ) -> Result<InstalledObservationManifest, ManifestFailure> {
        let mut specs = Vec::with_capacity(rules.len());
        let backend = rules
            .first()
            .map(|first| {
                Backend::new(
                    &side.artifacts.definition_kore,
                    &first.rule.module,
                    BackendOptions::default(),
                )
            })
            .transpose()
            .map_err(|_| ManifestFailure::Identity {
                rule: rules[0].rule.clone(),
                error: IdentityError::Missing,
            })?;
        for rule in rules {
            let sentence = self
                .baseline
                .sentence(&rule.rule)
                .filter(|sentence| matches!(sentence, Sentence::Rule { .. }))
                .filter(|_| {
                    self.baseline
                        .authored_sentences()
                        .any(|(at, _)| at == rule.rule)
                })
                .ok_or_else(|| ManifestFailure::UnknownRule(rule.rule.clone()))?;
            let attributes = sentence.attributes();
            let identity = match side.rule_identity_for(&rule.rule) {
                Ok(identity) => identity,
                Err(IdentityError::Missing)
                    if side.origins().is_some_and(|origins| {
                        !origins
                            .values()
                            .any(|origin| *origin == SentenceOrigin::Baseline(rule.rule.clone()))
                    }) =>
                {
                    continue;
                }
                Err(error) => {
                    return Err(ManifestFailure::Identity {
                        rule: rule.rule.clone(),
                        error,
                    });
                }
            };
            let backend = backend.as_ref().expect("nonempty rules created a backend");
            let catalog = backend.rule_catalog(Some(&rule.rule.module)).map_err(|_| {
                ManifestFailure::Identity {
                    rule: rule.rule.clone(),
                    error: IdentityError::Missing,
                }
            })?;
            if catalog
                .iter()
                .any(|entry| entry.id == identity && entry.shared_identity)
            {
                return Err(ManifestFailure::Identity {
                    rule: rule.rule.clone(),
                    error: IdentityError::Ambiguous,
                });
            }
            if !catalog.iter().any(|entry| {
                entry.id == identity && entry.kind == CompiledRuleKind::Rewrite && entry.executable
            }) {
                return Err(ManifestFailure::Identity {
                    rule: rule.rule.clone(),
                    error: IdentityError::Missing,
                });
            }
            specs.push(RuleObservationSpec {
                rule: rule.rule.clone(),
                label: attributes.string(AttributeKey::Label).map(str::to_owned),
                backend_rule_identity: identity.to_owned(),
                emit_rule_applied: rule.emit_rule_applied,
                domain_events: rule.domain_events.clone(),
            });
        }
        let mut authors = BTreeMap::new();
        for identity in specs
            .iter()
            .map(|spec| &spec.backend_rule_identity)
            .collect::<std::collections::BTreeSet<_>>()
        {
            let provenance = side
                .artifacts
                .sentence_provenance
                .get(identity)
                .ok_or_else(|| {
                    ManifestFailure::Installation(ObservationFailure::InvalidManifest(
                        "selected compiled identity has no typed provenance".into(),
                    ))
                })?;
            let mut positions = std::collections::BTreeSet::new();
            for address in &provenance.input_addresses {
                if address.input != InputSpace::Compile {
                    continue;
                }
                let position = SentenceRef::new(&address.module, address.index);
                if side.definition.modules.iter().any(|module| {
                    module.name == address.module
                        && module
                            .local_sentences
                            .get(address.index as usize)
                            .is_some_and(|sentence| matches!(&**sentence, Sentence::Rule { .. }))
                }) {
                    positions.insert(position);
                }
            }
            let observed = positions
                .into_iter()
                .map(|position| {
                    let baseline = side.origins.as_ref().map_or_else(
                        || Some(position.clone()),
                        |origins| match origins.get(&position) {
                            Some(SentenceOrigin::Baseline(at)) => Some(at.clone()),
                            Some(SentenceOrigin::Inserted { .. }) | None => None,
                        },
                    );
                    let spec = baseline
                        .as_ref()
                        .and_then(|at| specs.iter().find(|spec| &spec.rule == at).cloned());
                    AuthorObservation {
                        rule: position,
                        spec,
                    }
                })
                .collect();
            authors.insert(identity.clone(), observed);
        }
        InstalledObservationManifest::install_with_authors(specs, authors)
            .map_err(ManifestFailure::Installation)
    }

    fn compile(&self, loaded: &LoadedDefinition) -> Result<CompiledKoreArtifacts, CompileError> {
        compile_loaded_definition(loaded, self.options.clone())
    }
}

/// One written baseline rule to observe by its source position on every compiled side.
#[derive(Clone, Debug, PartialEq)]
pub struct ObservedRule {
    pub rule: SentenceRef,
    pub emit_rule_applied: bool,
    pub domain_events: Vec<DomainEventSpec>,
}

/// Why an observation manifest cannot be installed for a compiled side.
#[derive(Clone, Debug, PartialEq)]
pub enum ManifestFailure {
    /// The position is not an authored baseline rule: a declaration error.
    UnknownRule(SentenceRef),
    /// The position does not resolve to one compiled rule on this side, and the patch did
    /// not delete its baseline sentence.
    Identity {
        rule: SentenceRef,
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

    /// Compiled identity of a written sentence, joined by its compile input address.
    pub fn rule_identity_for(&self, at: &SentenceRef) -> Result<&str, IdentityError> {
        let positions = self.definition.modules.iter().flat_map(|module| {
            module
                .local_sentences
                .iter()
                .enumerate()
                .map(move |(index, _)| {
                    SentenceRef::new(
                        &module.name,
                        u32::try_from(index).expect("sentence index fits in u32"),
                    )
                })
        });
        let authors = positions
            .filter(|position| match &self.origins {
                Some(origins) => {
                    origins.get(position) == Some(&SentenceOrigin::Baseline(at.clone()))
                }
                None => position == at,
            })
            .collect::<Vec<_>>();
        let ids = self
            .artifacts
            .sentence_provenance
            .iter()
            .filter_map(|(id, provenance)| {
                provenance
                    .input_addresses
                    .iter()
                    .any(|address| {
                        address.input == InputSpace::Compile
                            && authors.iter().any(|author| {
                                author.module == address.module && author.index == address.index
                            })
                    })
                    .then_some(id.as_str())
            })
            .collect::<std::collections::BTreeSet<_>>();
        match ids.len() {
            0 => Err(IdentityError::Missing),
            1 => Ok(ids.into_iter().next().expect("one identity")),
            _ => Err(IdentityError::Ambiguous),
        }
    }

    /// Resolve a source and location to a written sentence, then use the typed relation.
    pub fn rule_identity(&self, source: &str, location: Location) -> Result<&str, IdentityError> {
        let positions = self
            .definition
            .modules
            .iter()
            .flat_map(|module| {
                module
                    .local_sentences
                    .iter()
                    .enumerate()
                    .filter(move |(_, sentence)| {
                        sentence.attributes().source() == Some(source)
                            && sentence.attributes().location() == Some(location)
                    })
                    .map(move |(index, _)| {
                        SentenceRef::new(
                            &module.name,
                            u32::try_from(index).expect("sentence index fits in u32"),
                        )
                    })
            })
            .collect::<Vec<_>>();
        match positions.as_slice() {
            [at] => self.rule_identity_for(at),
            [] => Err(IdentityError::Missing),
            _ => Err(IdentityError::Ambiguous),
        }
    }
}

/// Why a source position does not resolve to one compiled rule identity.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum IdentityError {
    /// No compiled rule carries the position, or it has no `UNIQUE_ID`.
    Missing,
    /// Several compiled rules share the position or its resolved `UNIQUE_ID`.
    Ambiguous,
}

impl fmt::Display for IdentityError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        formatter.write_str(match self {
            Self::Missing => "no compiled rule identity for the source position",
            Self::Ambiguous => "the source position does not have a unique compiled rule identity",
        })
    }
}

impl std::error::Error for IdentityError {}

#[cfg(test)]
use crate::support;

#[cfg(test)]
mod tests {
    use super::*;
    use crate::RewriteRules;

    #[test]
    fn all_transitions_uses_typed_provenance_without_source_attributes() {
        let validator =
            NativeValidator::bind(support::load("counter.k"), CompileOptions::default());
        let baseline = validator.compile_baseline().expect("baseline");
        let rule = support::rule(validator.baseline(), "COUNTER.increment");
        let attributes = validator
            .baseline()
            .sentence(&rule)
            .expect("rule")
            .attributes();
        let id = baseline
            .rule_identity(attributes.source().unwrap(), attributes.location().unwrap())
            .unwrap()
            .to_owned();
        #[rustfmt::skip]
        let rows = [
            ("missing-source", &[AttributeKey::Source][..]),
            ("missing-location", &[AttributeKey::Location][..]),
            ("missing-both", &[AttributeKey::Source, AttributeKey::Location][..]),
        ];
        for (name, keys) in rows {
            let mut side = baseline.clone();
            let sentence = side
                .artifacts
                .execution_definition
                .modules
                .iter_mut()
                .flat_map(|module| module.local_sentences.iter_mut())
                .find(|sentence| sentence.attributes().string(AttributeKey::UniqueId) == Some(&id))
                .expect("compiled rule");
            for key in keys {
                std::sync::Arc::make_mut(sentence)
                    .attributes_mut()
                    .remove(key.as_str());
            }
            assert_eq!(
                RewriteRules::classify(&validator, &side, "COUNTER"),
                RewriteRules::classify(&validator, &baseline, "COUNTER"),
                "{name}"
            );
        }
    }
}
