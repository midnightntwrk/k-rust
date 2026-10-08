//! Original-relative patches over a loaded k-rust [`Definition`].
//!
//! A [`Baseline`] is one immutable definition as `load_for_compilation`
//! returns it, where rule bodies are KAST terms rather than bubbles. Every
//! edit addresses that baseline by (module, sentence index, term path) and
//! carries the baseline value it expects. Selected patches also pin the version
//! of every addressed sentence; application checks these fingerprints first.
//! Addresses are stable within one baseline only.
//!
//! This crate performs local checks and name resolution only. Whether a
//! mutant compiles is decided by k-rust `compile_loaded_definition` over
//! [`Mutant::to_loaded`], which kink-native's validator runs.
//!
//! [`derive_sites`], [`select`] and [`Selection::fold`] turn the baseline's
//! term positions into a [`CandidateGeneration`] of deduplicated candidate
//! patches.
//!
//! [`ClaimSupport`] relates the attributes k-rust trusts without checking them to the
//! sentences they rest on, and [`ClaimSupport::withdraw`] removes from a mutant every such
//! claim whose support its patch touched.

mod apply;
mod candidate;
mod claims;
mod codec;
mod digest;
mod failure;
mod fingerprint;
mod semantic_input;
mod sort;
mod universe;

pub use apply::{Mutant, SentenceOrigin, apply};
pub use candidate::{
    Bindings, Candidate, CandidateDisposition, CandidateFailure, CandidateFailureKind,
    CandidateGeneration, Completeness, Discovery, DiscoveryTuple, PatchOrigin, Selection,
    SelectionPolicy, Site, SiteSelector, derive_sites, derive_sites_in, select,
};
pub use claims::{Claim, ClaimSupport, Withdrawal};
pub use codec::CodecError;
pub use digest::{
    CAMPAIGN_MANIFEST_DOMAIN, CANONICAL_PATCH_DOMAIN, COMPILED_KORE_DOMAIN, OBSERVATION_DOMAIN,
    Sha256Digest, StructureError, TEST_MANIFEST_DOMAIN, canonical_json, payload_digest, sha256,
    structure_sha256,
};
pub use failure::{PatchFailure, PatchFailureKind};
pub use fingerprint::{
    FINGERPRINT_DOMAIN, FingerprintError, POSITION_KEYS, SentenceFingerprint, fingerprint_payload,
};
pub use semantic_input::{SemanticInput, SemanticInputError};
pub use universe::{ExclusionReason, ResolvedUniverse, Universe, resolve_universe};

use k_rust::definition::{Definition, Sentence};
use k_rust::kast::Term;
use k_rust::kompile::CompileOptions;
use k_rust::outer::{
    LoadError, LoadOptions, LoadedDefinition, ResolvedSource, SourceResolver, load_for_compilation,
};
use serde_json::Value;
use std::collections::{BTreeMap, BTreeSet};
use std::fmt;

/// One immutable loaded baseline. Mutants are always relative to it.
#[derive(Clone, Debug)]
pub struct Baseline {
    loaded: LoadedDefinition,
}

impl Baseline {
    /// Wraps a definition already loaded by the caller, who owns prelude policy.
    #[must_use]
    pub const fn new(loaded: LoadedDefinition) -> Self {
        Self { loaded }
    }

    /// Loads through k-rust `load_for_compilation` with caller-supplied options.
    ///
    /// The syntax module name that k-rust also returns is dropped: it only
    /// matters for parsing programs, which kink never does.
    ///
    /// # Errors
    ///
    /// Returns the k-rust load error unchanged.
    pub fn load(
        entry: ResolvedSource,
        main_module: &str,
        syntax_module: Option<&str>,
        resolver: &mut impl SourceResolver,
        options: &LoadOptions,
    ) -> Result<Self, LoadError> {
        let (loaded, _syntax_module) =
            load_for_compilation(entry, main_module, syntax_module, resolver, options)?;
        Ok(Self::new(loaded))
    }

    #[must_use]
    pub const fn loaded(&self) -> &LoadedDefinition {
        &self.loaded
    }

    #[must_use]
    pub fn definition(&self) -> &Definition {
        self.loaded.definition()
    }

    #[must_use]
    pub fn sentence(&self, at: &SentenceRef) -> Option<&Sentence> {
        sentence_at(self.definition(), &at.module, at.index)
    }

    #[must_use]
    pub fn term(&self, at: &TermRef) -> Option<&Term> {
        term_at(
            self.definition(),
            &at.sentence.module,
            at.sentence.index,
            &at.path.0,
        )
    }

    /// Returns the version of an existing baseline sentence.
    ///
    /// # Errors
    ///
    /// A missing sentence is stale; an unsupported payload is locally ill-formed.
    pub fn fingerprint(&self, at: &SentenceRef) -> Result<SentenceFingerprint, PatchFailure> {
        let sentence = self.sentence(at).ok_or_else(|| {
            PatchFailure::new(
                PatchFailureKind::StalePrecondition,
                format!("{at:?} does not exist"),
            )
        })?;
        SentenceFingerprint::of(sentence).map_err(|error| {
            PatchFailure::new(PatchFailureKind::LocallyIllFormed, error.to_string())
        })
    }

    /// The user's written sentences: located and outside the builtin catalog,
    /// in definition order. This is the site universe for patches.
    ///
    /// Configuration expansion stamps an origin record on some written
    /// sentences (unlabelled rules among them), so an origin record does not
    /// mark a sentence as generated; its generated sentences (the init rules
    /// and productions) are the ones without a location. The cell productions
    /// it derives keep the configuration's location and are listed.
    pub fn authored_sentences(&self) -> impl Iterator<Item = (SentenceRef, &Sentence)> {
        let builtin_source_prefixes = CompileOptions::default().builtin_source_prefixes;
        self.definition().modules.iter().flat_map(move |module| {
            let builtin_source_prefixes = builtin_source_prefixes.clone();
            module
                .local_sentences
                .iter()
                .enumerate()
                .filter(move |(_, sentence)| {
                    let attributes = sentence.attributes();
                    attributes.location().is_some()
                        && !attributes.source().is_some_and(|source| {
                            builtin_source_prefixes
                                .iter()
                                .any(|prefix| source.starts_with(prefix))
                        })
                })
                .filter_map(|(index, sentence)| {
                    let index = u32::try_from(index).ok()?;
                    Some((SentenceRef::new(module.name.clone(), index), &**sentence))
                })
        })
    }
}

/// A sentence by its index in `FlatModule::local_sentences` of one baseline.
///
/// This is the (module, `sentence_index`) part of a k-rust
/// `provenance::DestinationAnchor`. Obtain it from a [`Baseline`], never by
/// counting source lines: loading moves configuration sentences.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct SentenceRef {
    pub module: String,
    pub index: u32,
}

impl SentenceRef {
    #[must_use]
    pub fn new(module: impl Into<String>, index: u32) -> Self {
        Self {
            module: module.into(),
            index,
        }
    }
}

/// A term path with `DestinationAnchor.path` semantics.
///
/// Step 0 selects the sentence field: body 0; requires 1 and ensures 2 for
/// rules and claims; requires 1 for contexts; ensures 1 for configurations.
/// Later steps select children: rewrite left 0 and right 1, as-pattern 0 and
/// alias 1, and the argument or item index of applications and sequences.
/// Compiler annotations are transparent, and semantic casts are ordinary
/// applications.
#[derive(Clone, Debug, Default, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermPath(pub Vec<u32>);

/// A mutation site: (module, sentence, term path) within one baseline.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub struct TermRef {
    pub sentence: SentenceRef,
    pub path: TermPath,
}

impl TermRef {
    #[must_use]
    pub fn new(sentence: SentenceRef, path: impl Into<Vec<u32>>) -> Self {
        Self {
            sentence,
            path: TermPath(path.into()),
        }
    }
}

/// Resolves a term position in any definition, including compiled ones.
///
/// It returns the stored term, with any compiler annotation still attached.
/// A coordinate read from a compiled definition's anchor is only meaningful
/// in that definition: compiler passes insert sentences and wrap terms.
#[must_use]
pub fn term_at<'a>(
    definition: &'a Definition,
    module: &str,
    index: u32,
    path: &[u32],
) -> Option<&'a Term> {
    path_in(sentence_at(definition, module, index)?, path)
}

fn sentence_at<'a>(definition: &'a Definition, module: &str, index: u32) -> Option<&'a Sentence> {
    definition
        .modules
        .iter()
        .find(|candidate| candidate.name == module)?
        .local_sentences
        .get(usize::try_from(index).ok()?)
        .map(|sentence| &**sentence)
}

fn path_in<'a>(sentence: &'a Sentence, path: &[u32]) -> Option<&'a Term> {
    let (field, steps) = path.split_first()?;
    let mut term = field_term(sentence, *field)?;
    for step in steps {
        term = child(term, *step)?;
    }
    Some(term)
}

fn field_term(sentence: &Sentence, field: u32) -> Option<&Term> {
    match (sentence, field) {
        (
            Sentence::Rule { body, .. }
            | Sentence::Claim { body, .. }
            | Sentence::Context { body, .. }
            | Sentence::ContextAlias { body, .. }
            | Sentence::Configuration { body, .. },
            0,
        ) => Some(body),
        (
            Sentence::Rule { requires, .. }
            | Sentence::Claim { requires, .. }
            | Sentence::Context { requires, .. }
            | Sentence::ContextAlias { requires, .. },
            1,
        ) => Some(requires),
        (Sentence::Configuration { ensures, .. }, 1)
        | (Sentence::Rule { ensures, .. } | Sentence::Claim { ensures, .. }, 2) => Some(ensures),
        _ => None,
    }
}

fn child(term: &Term, step: u32) -> Option<&Term> {
    let step = usize::try_from(step).ok()?;
    match term.unannotated() {
        Term::Rewrite { left, right } => [left, right].get(step).map(|child| &***child),
        Term::As { pattern, alias } => [pattern, alias].get(step).map(|child| &***child),
        Term::Apply { arguments, .. } | Term::Sequence(arguments) => arguments.get(step),
        _ => None,
    }
}

/// One original-relative edit.
///
/// `expected` values are ordinary baseline values that the edit's author
/// read, compared with `Term` equality (metadata-insensitive) or JSON
/// equality. They are preconditions, not identities.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum Edit {
    /// A one-step path replaces a whole field; `[1]` and `[2]` replace a
    /// condition, whose expected sort is `Bool`.
    ReplaceTerm {
        at: TermRef,
        expected: Term,
        replacement: Term,
    },
    /// The replacement keeps the baseline variant, label and position
    /// attributes.
    ReplaceSentence {
        at: SentenceRef,
        replacement: Sentence,
    },
    DeleteSentence {
        at: SentenceRef,
    },
    /// Inserted sentences carry no protected identity or source-position attributes.
    /// Several insertions at one position are placed by ascending `ordinal`.
    InsertSentence {
        position: InsertPosition,
        ordinal: u32,
        sentence: Sentence,
    },
    /// Never overwrites: the key must be absent.
    AddAttribute {
        at: SentenceRef,
        key: String,
        value: Value,
    },
    RemoveAttribute {
        at: SentenceRef,
        key: String,
        expected: Value,
    },
    ReplaceAttribute {
        at: SentenceRef,
        key: String,
        expected: Value,
        replacement: Value,
    },
}

/// Where an inserted sentence goes, in baseline coordinates.
#[derive(Clone, Debug, Eq, Hash, Ord, PartialEq, PartialOrd)]
pub enum InsertPosition {
    Before(SentenceRef),
    After(SentenceRef),
    ModuleStart(String),
    ModuleEnd(String),
}

/// The part of a baseline sentence an edit writes. Declaration order is the
/// canonical order.
#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Region<'a> {
    Sentence,
    Attribute(&'a str),
    Term(&'a [u32]),
}

#[derive(Clone, Copy, Debug, Eq, Ord, PartialEq, PartialOrd)]
enum Target<'a> {
    Existing(&'a SentenceRef, Region<'a>),
    Slot(&'a InsertPosition, u32),
}

impl Edit {
    fn target(&self) -> Target<'_> {
        match self {
            Self::ReplaceTerm { at, .. } => {
                Target::Existing(&at.sentence, Region::Term(&at.path.0))
            }
            Self::ReplaceSentence { at, .. } | Self::DeleteSentence { at } => {
                Target::Existing(at, Region::Sentence)
            }
            Self::AddAttribute { at, key, .. }
            | Self::RemoveAttribute { at, key, .. }
            | Self::ReplaceAttribute { at, key, .. } => {
                Target::Existing(at, Region::Attribute(key))
            }
            Self::InsertSentence {
                position, ordinal, ..
            } => Target::Slot(position, *ordinal),
        }
    }

    const fn rank(&self) -> u8 {
        match self {
            Self::ReplaceTerm { .. } => 0,
            Self::ReplaceSentence { .. } => 1,
            Self::DeleteSentence { .. } => 2,
            Self::InsertSentence { .. } => 3,
            Self::AddAttribute { .. } => 4,
            Self::RemoveAttribute { .. } => 5,
            Self::ReplaceAttribute { .. } => 6,
        }
    }
}

/// A non-empty, canonically ordered edit list.
///
/// Patch equality is the deduplication key: permuted inputs build equal
/// patches.
#[derive(Clone, Debug, Eq, PartialEq)]
pub struct Patch {
    edits: Vec<Edit>,
    pins: BTreeMap<SentenceRef, SentenceFingerprint>,
    pinned: bool,
}

impl Patch {
    /// Orders edits by (target, operation).
    ///
    /// Two edits compare equal on that key only when they share a target,
    /// which `apply` always rejects as `DuplicateTarget`; their debug
    /// rendering breaks the tie so that such patches are permutation-invariant
    /// too.
    ///
    /// # Errors
    ///
    /// Rejects an empty edit list.
    pub fn new(mut edits: Vec<Edit>) -> Result<Self, PatchModelError> {
        if edits.is_empty() {
            return Err(PatchModelError::Empty);
        }
        edits.sort_by(|left, right| {
            (left.target(), left.rank())
                .cmp(&(right.target(), right.rank()))
                .then_with(|| format!("{left:?}").cmp(&format!("{right:?}")))
        });
        Ok(Self {
            edits,
            pins: BTreeMap::new(),
            pinned: false,
        })
    }

    /// Every existing sentence addressed by an edit or insertion anchor.
    #[must_use]
    pub fn addressed_sentences(&self) -> Vec<SentenceRef> {
        let mut sentences = self
            .written_sentences()
            .into_iter()
            .collect::<BTreeSet<_>>();
        for edit in &self.edits {
            if let Edit::InsertSentence {
                position: InsertPosition::Before(at) | InsertPosition::After(at),
                ..
            } = edit
            {
                sentences.insert(at.clone());
            }
        }
        sentences.into_iter().collect()
    }

    /// Records the baseline version of every addressed sentence.
    ///
    /// # Errors
    ///
    /// Refuses missing or unsupported sentences and a stale existing pin.
    pub fn pinned(mut self, baseline: &Baseline) -> Result<Self, PatchFailure> {
        for at in self.addressed_sentences() {
            let current = baseline.fingerprint(&at)?;
            if let Some(pin) = self.pins.get(&at)
                && *pin != current
            {
                return Err(PatchFailure::new(
                    PatchFailureKind::StalePrecondition,
                    format!("{at:?} has fingerprint {current}, not {pin}"),
                ));
            }
            self.pins.insert(at, current);
        }
        self.pinned = true;
        Ok(self)
    }

    /// Constructs a pinned patch with exact, unique coverage of its addresses.
    ///
    /// # Errors
    ///
    /// Refuses empty edits or missing, repeated, or extra pins.
    pub fn with_pins(
        edits: Vec<Edit>,
        pins: Vec<(SentenceRef, SentenceFingerprint)>,
    ) -> Result<Self, PatchModelError> {
        let mut patch = Self::new(edits)?;
        let count = pins.len();
        patch.pins = pins.into_iter().collect();
        if patch.pins.len() != count
            || patch.pins.keys().cloned().collect::<Vec<_>>() != patch.addressed_sentences()
        {
            return Err(PatchModelError::PinMismatch);
        }
        patch.pinned = true;
        Ok(patch)
    }

    #[must_use]
    pub const fn pins(&self) -> &BTreeMap<SentenceRef, SentenceFingerprint> {
        &self.pins
    }

    #[must_use]
    pub const fn is_pinned(&self) -> bool {
        self.pinned
    }

    #[must_use]
    pub fn edits(&self) -> &[Edit] {
        &self.edits
    }

    /// Distinct existing baseline sentences written by this patch, in sentence order.
    /// Insertions are not listed.
    #[must_use]
    pub fn written_sentences(&self) -> Vec<SentenceRef> {
        let mut sentences = self
            .edits
            .iter()
            .filter_map(|edit| match edit {
                Edit::ReplaceTerm { at, .. } => Some(at.sentence.clone()),
                Edit::ReplaceSentence { at, .. }
                | Edit::DeleteSentence { at }
                | Edit::AddAttribute { at, .. }
                | Edit::RemoveAttribute { at, .. }
                | Edit::ReplaceAttribute { at, .. } => Some(at.clone()),
                Edit::InsertSentence { .. } => None,
            })
            .collect::<Vec<_>>();
        sentences.sort();
        sentences.dedup();
        sentences
    }
}

/// A patch that cannot be constructed.
#[derive(Clone, Copy, Debug, Eq, PartialEq)]
pub enum PatchModelError {
    Empty,
    PinMismatch,
}

impl fmt::Display for PatchModelError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("a patch has at least one edit"),
            Self::PinMismatch => {
                formatter.write_str("pins must cover addressed sentences exactly once")
            }
        }
    }
}

impl std::error::Error for PatchModelError {}
