use std::{collections::BTreeMap, error::Error, fmt};

use krs_diagnostic::{Diagnostic, Location, ToDiagnostic, codes};
use krs_ir::{DefinitionIr, DefinitionSentence, NodeOrigin, SourceMapKey};

use crate::{
    EmittedSentenceProvenance, GeneratingPass, InputAddress, InputSentenceKind, InputSpace,
    LoadedDefinition,
    adapter::{AdaptedDefinition, NativeNodePlace, SentenceNodeRole},
};

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
pub(super) fn join_sentence_provenance(
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

#[cfg(test)]
mod tests;
