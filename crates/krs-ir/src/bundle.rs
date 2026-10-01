//! Serializable collector output.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;
use std::io::Write;

use serde::{Deserialize, Deserializer, Serialize};

use crate::stage::{DescriptorStage, stage_shape};
use crate::transport::detail::TransportField;
use crate::transport::{
    configuration::{FixedConfiguration as TransportFixedConfiguration, StageCellDeclaration},
    grammar::{StageGrammarDescriptor, StructuredRule},
    rule::{ConfigurationRule, ContextAlias},
};

use crate::sorted::{SortKey, SortedByKey};
use crate::{
    ExplicitSymbol, GrammarTransportError, OriginStack, ProvenanceKey, ProvenanceRole,
    RustVisibility, SchemaVersion, StableItemId, StateTransportError, StructuredRuleDescriptor,
};

impl SortKey for Descriptor {
    type Key = Self;
    fn sort_key(&self) -> &Self::Key {
        self
    }
}

impl SortKey for DescriptorDeclaration {
    type Key = Self;
    fn sort_key(&self) -> &Self::Key {
        self
    }
}

impl SortKey for DescriptorNodeOrigin {
    type Key = ProvenanceKey;
    fn sort_key(&self) -> &Self::Key {
        &self.key
    }
}

/// Deterministic, serializable output of one host collector execution.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DescriptorBundle {
    /// Schema and canonical-encoding version.
    protocol_version: SchemaVersion,
    /// Collected descriptors in their full derived order.
    pub descriptors: SortedByKey<Descriptor>,
    /// Exact Rust API metadata for every collected descriptor.
    pub declarations: SortedByKey<DescriptorDeclaration>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DescriptorBundleWire {
    protocol_version: SchemaVersion,
    descriptors: Vec<Descriptor>,
    declarations: Vec<DescriptorDeclaration>,
}

impl<'de> Deserialize<'de> for DescriptorBundle {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = DescriptorBundleWire::deserialize(deserializer)?;
        if wire.protocol_version != SchemaVersion::CURRENT {
            return Err(serde::de::Error::custom(format_args!(
                "unsupported descriptor bundle schema {}; expected {}",
                wire.protocol_version.0,
                SchemaVersion::CURRENT.0
            )));
        }
        for descriptor in &wire.descriptors {
            descriptor
                .validate_grammar_contract()
                .map_err(serde::de::Error::custom)?;
            descriptor
                .validate_state_contract()
                .map_err(serde::de::Error::custom)?;
        }
        validate_declarations(&wire.descriptors, &wire.declarations)
            .map_err(serde::de::Error::custom)?;
        Ok(Self {
            protocol_version: wire.protocol_version,
            descriptors: SortedByKey::new(wire.descriptors),
            declarations: SortedByKey::new(wire.declarations),
        })
    }
}

impl DescriptorBundle {
    /// Creates a bundle using the only protocol this crate can write.
    #[must_use]
    pub fn new(descriptors: Vec<Descriptor>) -> Self {
        let declarations = descriptors
            .iter()
            .map(|descriptor| DescriptorDeclaration {
                id: descriptor.id.clone(),
                visibility: RustVisibility::Inherited,
                explicit_symbol: None,
            })
            .collect();
        Self {
            protocol_version: SchemaVersion::CURRENT,
            descriptors: SortedByKey::new(descriptors),
            declarations: SortedByKey::new(declarations),
        }
    }

    /// Creates a bundle with parser-recovered exact declaration metadata.
    ///
    /// # Errors
    ///
    /// Rejects missing, duplicate, or extra declaration metadata entries.
    pub fn with_declarations(
        descriptors: Vec<Descriptor>,
        declarations: Vec<DescriptorDeclaration>,
    ) -> Result<Self, DescriptorDeclarationError> {
        validate_declarations(&descriptors, &declarations)?;
        Ok(Self {
            protocol_version: SchemaVersion::CURRENT,
            descriptors: SortedByKey::new(descriptors),
            declarations: SortedByKey::new(declarations),
        })
    }

    /// Rebuilds every set-like bundle collection from permuted inputs.
    ///
    /// # Panics
    ///
    /// Panics if this validated bundle cannot be rebuilt.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut descriptors = self
            .descriptors
            .iter()
            .map(|descriptor| descriptor.permute_sets(seed))
            .collect::<Vec<_>>();
        let mut declarations = self.declarations.iter().cloned().collect::<Vec<_>>();
        crate::testing::permute(&mut descriptors, seed);
        crate::testing::permute(&mut declarations, seed);
        Self::with_declarations(descriptors, declarations).unwrap_or_else(|error| {
            panic!("DescriptorBundle seed {seed}: permuted rebuild failed: {error}")
        })
    }

    /// Creates an empty bundle using the current protocol.
    #[must_use]
    pub fn empty() -> Self {
        Self::new(Vec::new())
    }

    /// Returns the canonical descriptor-bundle schema version.
    #[must_use]
    pub const fn protocol_version(&self) -> SchemaVersion {
        self.protocol_version
    }

    /// Returns exact declaration API metadata for one stable descriptor ID.
    #[must_use]
    pub fn declaration(&self, id: &StableItemId) -> Option<&DescriptorDeclaration> {
        self.declarations
            .iter()
            .find(|declaration| declaration.id() == id)
    }

    /// Returns canonical, inspectable JSON with one trailing newline.
    ///
    /// Descriptor and declaration orders are canonical in the bundle value.
    ///
    /// # Errors
    ///
    /// Returns an error if this protocol's serde data model cannot be encoded
    /// as JSON. Current descriptor variants contain no fallible JSON values.
    pub fn to_canonical_json(&self) -> serde_json::Result<String> {
        let mut json = serde_json::to_string_pretty(self)?;
        json.push('\n');
        Ok(json)
    }

    /// Serializes this bundle as compact collector protocol JSON with
    /// one trailing newline and counts bytes encoding `provenance` values.
    ///
    /// # Errors
    ///
    /// Returns an error if the bundle cannot be encoded as JSON.
    pub fn to_collector_protocol_measured(&self) -> serde_json::Result<(Vec<u8>, u64)> {
        let mut writer = crate::measure::ProvenanceCountingWriter {
            bytes: Vec::with_capacity(self.json_capacity_hint()),
            provenance: 0,
        };
        crate::transport::collector::write(self, &mut writer)?;
        writer.write_all(b"\n").map_err(serde_json::Error::io)?;
        Ok((writer.bytes, writer.provenance))
    }

    /// Writes compact canonical collector protocol JSON.
    ///
    /// # Errors
    ///
    /// Returns an error if JSON encoding or the destination write fails.
    pub fn write_collector_protocol(&self, mut writer: impl Write) -> serde_json::Result<()> {
        crate::transport::collector::write(self, &mut writer)?;
        writer.write_all(b"\n").map_err(serde_json::Error::io)
    }

    /// Decodes the versioned collector wire into the canonical bundle model.
    ///
    /// # Errors
    ///
    /// Rejects malformed JSON, invalid table indexes, frame codes, and bundle contracts.
    pub fn from_collector_protocol(bytes: &[u8]) -> serde_json::Result<Self> {
        crate::transport::collector::decode(bytes)
    }

    fn json_capacity_hint(&self) -> usize {
        // Reserve for compact frames and the unchanged descriptor payloads.
        let origins = self.descriptors.iter().fold(0usize, |count, descriptor| {
            count.saturating_add(descriptor.provenance.origins().len())
        });
        origins
            .saturating_mul(160)
            .saturating_add(self.descriptors.len().saturating_mul(4 * 1024))
            .min(64 * 1024 * 1024)
    }
}

impl Default for DescriptorBundle {
    fn default() -> Self {
        Self::empty()
    }
}

/// Exact author-facing API metadata associated with one descriptor.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorDeclaration {
    /// Descriptor receiving this metadata.
    id: StableItemId,
    /// Exact authored Rust visibility.
    pub visibility: RustVisibility,
    /// Optional stable public identity override.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub explicit_symbol: Option<ExplicitSymbol>,
}

impl DescriptorDeclaration {
    /// Creates exact metadata for one descriptor.
    #[must_use]
    pub const fn new(
        id: StableItemId,
        visibility: RustVisibility,
        explicit_symbol: Option<ExplicitSymbol>,
    ) -> Self {
        Self {
            id,
            visibility,
            explicit_symbol,
        }
    }

    /// Returns the descriptor identity receiving this metadata.
    #[must_use]
    pub const fn id(&self) -> &StableItemId {
        &self.id
    }
}

/// Invalid bundle-wide declaration metadata coverage.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DescriptorDeclarationError {
    /// Metadata was missing for a descriptor.
    Missing(Box<StableItemId>),
    /// Metadata named an ID not present in the descriptor set.
    Extra(Box<StableItemId>),
    /// An ID received more than one metadata entry.
    Duplicate(Box<StableItemId>),
    /// An explicit symbol had no exact parser-owned origin.
    MissingSymbolOrigin(Box<StableItemId>),
    /// A stable-symbol origin existed without explicit symbol metadata.
    UnexpectedSymbolOrigin(Box<StableItemId>),
}

impl fmt::Display for DescriptorDeclarationError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing(id) => write!(formatter, "missing declaration metadata for {id}"),
            Self::Extra(id) => write!(formatter, "declaration metadata names unknown {id}"),
            Self::Duplicate(id) => write!(formatter, "duplicate declaration metadata for {id}"),
            Self::MissingSymbolOrigin(id) => {
                write!(
                    formatter,
                    "explicit symbol metadata for {id} has no exact origin"
                )
            }
            Self::UnexpectedSymbolOrigin(id) => write!(
                formatter,
                "stable-symbol origin for {id} has no explicit symbol metadata"
            ),
        }
    }
}

impl Error for DescriptorDeclarationError {}

fn validate_declarations(
    descriptors: &[Descriptor],
    declarations: &[DescriptorDeclaration],
) -> Result<(), DescriptorDeclarationError> {
    let descriptor_ids = descriptors
        .iter()
        .map(|descriptor| descriptor.id.clone())
        .collect::<BTreeSet<_>>();
    let mut declaration_ids = BTreeSet::new();
    for declaration in declarations {
        if !descriptor_ids.contains(declaration.id()) {
            return Err(DescriptorDeclarationError::Extra(Box::new(
                declaration.id().clone(),
            )));
        }
        if !declaration_ids.insert(declaration.id().clone()) {
            return Err(DescriptorDeclarationError::Duplicate(Box::new(
                declaration.id().clone(),
            )));
        }
        let descriptor = descriptors
            .iter()
            .find(|descriptor| descriptor.id == *declaration.id())
            .expect("metadata IDs were checked against the descriptor set");
        let has_symbol_origin = descriptor.provenance.origins().iter().any(|origin| {
            origin.key.role() == ProvenanceRole::StableSymbol && origin.key.ordinal() == 0
        });
        if declaration.explicit_symbol.is_some() != has_symbol_origin {
            return Err(if declaration.explicit_symbol.is_some() {
                DescriptorDeclarationError::MissingSymbolOrigin(Box::new(declaration.id().clone()))
            } else {
                DescriptorDeclarationError::UnexpectedSymbolOrigin(Box::new(
                    declaration.id().clone(),
                ))
            });
        }
    }
    if let Some(missing) = descriptor_ids.difference(&declaration_ids).next() {
        return Err(DescriptorDeclarationError::Missing(Box::new(
            missing.clone(),
        )));
    }
    Ok(())
}

/// One stable declaration and its macro payload.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct Descriptor {
    /// Stable identity resolved before serialization.
    pub id: StableItemId,
    /// Enabled cfg keys and their optional values.
    pub cfg: BTreeMap<String, Option<String>>,
    /// Every parser-keyed authored node, including the primary declaration.
    pub provenance: DescriptorProvenance,
    /// Declaration-specific data containing stable references only.
    #[serde(flatten)]
    pub payload: DescriptorPayload,
}

impl Descriptor {
    /// Rebuilds the descriptor's set-like provenance and payload collections.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let payload = match &self.payload {
            DescriptorPayload::Sort(sort) => DescriptorPayload::Sort(sort.permute_sets(seed)),
            other => other.clone(),
        };
        Self {
            provenance: self.provenance.permute_sets(seed),
            payload,
            ..self.clone()
        }
    }

    /// Returns the primary declaration's authored-to-descriptor provenance.
    #[must_use]
    pub fn origin(&self) -> &OriginStack {
        self.provenance.primary_origin()
    }

    /// Validates typed grammar or structured-rule payloads.
    ///
    /// # Errors
    ///
    /// Returns [`GrammarTransportError`] for invalid ownership, shape,
    /// references, or parser keys absent from this descriptor's provenance.
    pub fn validate_grammar_contract(&self) -> Result<(), GrammarTransportError> {
        let contains = |key: &ProvenanceKey| self.provenance.origin_for(key).is_some();
        let (expected, expected_primary) = match &self.payload {
            DescriptorPayload::Grammar(grammar) => {
                grammar.validate(self.id.item_kind(), contains)?;
                (
                    Some(grammar.expected_provenance_keys()?),
                    Some(grammar.expected_primary_key()),
                )
            }
            DescriptorPayload::StructuredRule(rule) => {
                rule.validate(self.id.item_kind(), contains)?;
                (
                    Some(rule.expected_provenance_keys()?),
                    Some(StructuredRuleDescriptor::expected_primary_key()),
                )
            }
            DescriptorPayload::Sort(_)
            | DescriptorPayload::Constructor(_)
            | DescriptorPayload::FixedConfiguration(_)
            | DescriptorPayload::Cell(_)
            | DescriptorPayload::ConfigurationRule(_)
            | DescriptorPayload::HeadRule(_)
            | DescriptorPayload::ContextAlias(_) => (None, None),
        };
        let Some(expected) = expected else {
            return Ok(());
        };
        let actual = self
            .provenance
            .origins()
            .iter()
            .filter(|origin| origin.key.role() != ProvenanceRole::StableSymbol)
            .map(|origin| origin.key.clone())
            .collect::<BTreeSet<_>>();
        if let Some(missing) = expected.difference(&actual).next() {
            return Err(GrammarTransportError::MissingProvenance(missing.clone()));
        }
        if let Some(unexpected) = actual.difference(&expected).next() {
            return Err(GrammarTransportError::ExtraProvenance(unexpected.clone()));
        }
        let Some(expected_primary) = expected_primary else {
            return Err(GrammarTransportError::EmptyCollection(
                TransportField::RequiredGrammarPrimaryProvenanceKey,
            ));
        };
        if self.provenance.primary_key() != &expected_primary {
            return Err(GrammarTransportError::UnexpectedProvenance {
                expected: expected_primary,
                actual: self.provenance.primary_key().clone(),
            });
        }
        Ok(())
    }

    /// Validates fixed configurations, nominal cells, and
    /// simultaneous configuration rules against exact closed provenance.
    ///
    /// # Errors
    ///
    /// Returns [`StateTransportError`] for wrong ownership, invalid typed
    /// state, frame/binding errors, or missing/extra parser keys.
    pub fn validate_state_contract(&self) -> Result<(), StateTransportError> {
        let actual = self
            .provenance
            .origins()
            .iter()
            .map(|origin| origin.key.clone())
            .collect::<BTreeSet<_>>();
        match &self.payload {
            DescriptorPayload::FixedConfiguration(configuration) => configuration
                .validate_complete_provenance(&self.id, self.provenance.primary_key(), &actual),
            DescriptorPayload::Cell(declaration) => declaration.validate_complete_provenance(
                &self.id,
                self.provenance.primary_key(),
                &actual,
            ),
            DescriptorPayload::ConfigurationRule(rule) => rule.validate_complete_provenance(
                self.id.item_kind(),
                self.provenance.primary_key(),
                &actual,
            ),
            DescriptorPayload::HeadRule(rule) => rule.validate(self.id.item_kind()),
            DescriptorPayload::ContextAlias(alias) => alias.validate_complete_provenance(
                self.id.item_kind(),
                self.provenance.primary_key(),
                &actual,
            ),
            DescriptorPayload::Sort(_)
            | DescriptorPayload::Constructor(_)
            | DescriptorPayload::Grammar(_)
            | DescriptorPayload::StructuredRule(_) => Ok(()),
        }
    }
}

/// One exact parser-owned node origin in a stable descriptor.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct DescriptorNodeOrigin {
    /// Shared-parser semantic role and AST-order ordinal.
    pub key: ProvenanceKey,
    /// Authored range followed by invocation and descriptor transformations.
    pub origin: OriginStack,
}

impl DescriptorNodeOrigin {
    /// Associates one parser key with its materialized origin stack.
    #[must_use]
    pub const fn new(key: ProvenanceKey, origin: OriginStack) -> Self {
        Self { key, origin }
    }
}

/// Complete stable provenance for one descriptor.
///
/// The table retains every range materialized from [`crate::HostProvenance`],
/// rather than discarding all but the declaration range. A configuration may
/// merge nodes from its struct attribute and its associated initializer
/// attribute even when they occur in different source files.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd)]
pub struct DescriptorProvenance {
    primary_key: ProvenanceKey,
    origins: SortedByKey<DescriptorNodeOrigin>,
}

/// Borrowed serialization form of [`DescriptorProvenance`], field for field.
#[derive(Serialize)]
#[serde(rename = "DescriptorProvenance")]
struct DescriptorProvenanceRef<'a> {
    primary_key: &'a ProvenanceKey,
    origins: &'a [DescriptorNodeOrigin],
}

impl Serialize for DescriptorProvenance {
    fn serialize<S>(&self, serializer: S) -> Result<S::Ok, S::Error>
    where
        S: serde::Serializer,
    {
        // The scope lets a measuring writer attribute these bytes; it changes
        // nothing about the encoding.
        let _scope = crate::measure::ProvenanceScope::enter();
        DescriptorProvenanceRef {
            primary_key: &self.primary_key,
            origins: &self.origins,
        }
        .serialize(serializer)
    }
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DescriptorProvenanceWire {
    primary_key: ProvenanceKey,
    origins: Vec<DescriptorNodeOrigin>,
}

impl<'de> Deserialize<'de> for DescriptorProvenance {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = DescriptorProvenanceWire::deserialize(deserializer)?;
        Self::new(wire.primary_key, wire.origins).map_err(serde::de::Error::custom)
    }
}

impl DescriptorProvenance {
    /// Creates a nonempty table with unique keys and one declared primary key.
    ///
    /// # Errors
    ///
    /// Returns [`DescriptorProvenanceError`] when the table is empty, repeats
    /// a parser key, or does not contain `primary_key` exactly once.
    pub fn new(
        primary_key: ProvenanceKey,
        origins: Vec<DescriptorNodeOrigin>,
    ) -> Result<Self, DescriptorProvenanceError> {
        if origins.is_empty() {
            return Err(DescriptorProvenanceError::Empty);
        }
        let mut keys = BTreeSet::new();
        for node in &origins {
            if !keys.insert(node.key.clone()) {
                return Err(DescriptorProvenanceError::DuplicateKey(node.key.clone()));
            }
        }
        if !keys.contains(&primary_key) {
            return Err(DescriptorProvenanceError::MissingPrimary(primary_key));
        }
        Ok(Self {
            primary_key,
            origins: SortedByKey::new(origins),
        })
    }

    /// Rebuilds the parser-owned origin set from a permuted input.
    ///
    /// # Panics
    ///
    /// Panics if this validated provenance cannot be rebuilt.
    #[cfg(feature = "test-support")]
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut origins = self.origins.iter().cloned().collect::<Vec<_>>();
        crate::testing::permute(&mut origins, seed);
        Self::new(self.primary_key.clone(), origins).unwrap_or_else(|error| {
            panic!("DescriptorProvenance seed {seed}: permuted rebuild failed: {error}")
        })
    }

    /// Returns the parser key identifying the descriptor's declaration node.
    #[must_use]
    pub const fn primary_key(&self) -> &ProvenanceKey {
        &self.primary_key
    }

    /// Returns the primary declaration's origin stack.
    ///
    /// # Panics
    ///
    /// Panics only if this type's private validated primary-key invariant was
    /// violated by an internal implementation defect.
    #[must_use]
    pub fn primary_origin(&self) -> &OriginStack {
        self.origin_for(&self.primary_key)
            .expect("validated descriptor provenance contains its primary key")
    }

    /// Looks up one exact parser-owned node.
    #[must_use]
    pub fn origin_for(&self, key: &ProvenanceKey) -> Option<&OriginStack> {
        self.origins
            .iter()
            .find(|node| &node.key == key)
            .map(|node| &node.origin)
    }

    /// Returns parser-owned node origins. Their order has no semantic meaning.
    #[must_use]
    pub fn origins(&self) -> &[DescriptorNodeOrigin] {
        &self.origins
    }
}

/// Invalid descriptor-wide parser-keyed provenance.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum DescriptorProvenanceError {
    /// No parser node origin was retained.
    Empty,
    /// Two ranges claimed the same parser role and ordinal.
    DuplicateKey(ProvenanceKey),
    /// The selected primary key was absent from the table.
    MissingPrimary(ProvenanceKey),
}

impl fmt::Display for DescriptorProvenanceError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Empty => formatter.write_str("descriptor provenance table must not be empty"),
            Self::DuplicateKey(key) => write!(
                formatter,
                "duplicate descriptor provenance key `{}#{}`",
                key.role(),
                key.ordinal()
            ),
            Self::MissingPrimary(key) => write!(
                formatter,
                "descriptor provenance lacks primary key `{}#{}`",
                key.role(),
                key.ordinal()
            ),
        }
    }
}

impl Error for DescriptorProvenanceError {}

stage_shape! {
    /// Matching collector declaration payloads across reference stages.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        tag = "descriptor_kind",
        content = "descriptor",
        rename_all = "snake_case",
        deny_unknown_fields
    )]
    #[serde(
        rename = "DescriptorPayload",
        bound(
            serialize = "
                S::Parents: Serialize,
                S::ConstructorSort: Serialize,
                S::ConstructorFieldSort: Serialize,
                S::Sort: Serialize,
                S::Application: Serialize,
                S::Nominal: Serialize,
                S::ContextAlias: Serialize,
                S::Configuration: Serialize,
                S::Cell: Serialize,
                S::CellDeclaration: Serialize,
                S::InitializerOwner: Serialize,
                H: Serialize
            ",
            deserialize = "
                S::Parents: Deserialize<'de>,
                S::ConstructorSort: Deserialize<'de>,
                S::ConstructorFieldSort: Deserialize<'de>,
                S::Sort: Deserialize<'de>,
                S::Application: Deserialize<'de>,
                S::Nominal: Deserialize<'de>,
                S::ContextAlias: Deserialize<'de>,
                S::Configuration: Deserialize<'de>,
                S::Cell: Deserialize<'de>,
                S::CellDeclaration: Deserialize<'de>,
                S::InitializerOwner: Deserialize<'de>,
                H: Deserialize<'de>
            "
        )
    )]
    pub enum Payload<S: Stage, H => head => H2> {
        /// Open-sort declaration.
        Sort(value: SortPayload<S> => [nested]),
        /// Constructor declaration.
        Constructor(value: Constructor<S> => [nested]),
        /// Typed after-the-fact object-grammar sentence.
        Grammar(value: Box<StageGrammarDescriptor<S>> => [box nested]),
        /// Fully structured relational sentence using typed term references.
        StructuredRule(value: Box<StructuredRule<S>> => [box nested]),
        /// Complete fixed configuration and initializer.
        FixedConfiguration(value: Box<TransportFixedConfiguration<S>> => [box nested]),
        /// Nominal nested fixed-cell declaration.
        Cell(value: Box<StageCellDeclaration<S>> => [box with (crate::transport::configuration::map_declaration) S]),
        /// Simultaneous whole-configuration rule.
        ConfigurationRule(value: Box<ConfigurationRule<S>> => [box nested]),
        /// Computation-head rule before or after collector completion.
        HeadRule(value: Box<H> => [box via head]),
        /// One-sided reusable fixed-configuration context template.
        ContextAlias(value: Box<ContextAlias<S>> => [box nested]),
    }
}

/// Stable payload with a collector-completed head rule.
pub type DescriptorPayload = Payload<DescriptorStage, crate::DescriptorHeadRule>;

stage_shape! {
    /// Open-sort payload with direct parent references.
    #[derive(Clone, Debug, Default, Serialize, Deserialize)]
    #[serde(
        rename = "SortDescriptor",
        bound(
            serialize = "S::Parents: Serialize",
            deserialize = "S::Parents: Deserialize<'de>"
        )
    )]
    pub struct SortPayload<S: Stage> {
        /// Direct super-sort references in the stage's collection order.
        pub parents: S::Parents => [parents],
    }
}

/// Stable descriptor-stage form of [`SortPayload`].
pub type SortDescriptor = SortPayload<DescriptorStage>;

#[cfg(feature = "test-support")]
impl SortDescriptor {
    /// Rebuilds the direct parent-sort set from a permuted input.
    #[must_use]
    pub fn permute_sets(&self, seed: u64) -> Self {
        let mut parents = self.parents.iter().cloned().collect::<Vec<_>>();
        crate::testing::permute(&mut parents, seed);
        Self {
            parents: parents.into_iter().collect(),
        }
    }
}

stage_shape! {
    /// Constructor payload with result-sort and ordered field references.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "ConstructorDescriptor",
        bound(
            serialize = "S::ConstructorSort: Serialize, S::ConstructorFieldSort: Serialize",
            deserialize = "S::ConstructorSort: Deserialize<'de>, S::ConstructorFieldSort: Deserialize<'de>"
        )
    )]
    pub struct Constructor<S: Stage> {
        /// Sort directly containing the constructor.
        pub sort: S::ConstructorSort => [constructor_sort],
        /// Fields in authored constructor order.
        pub fields: Vec<ConstructorField<S>> => [vec nested],
    }
}

/// Stable descriptor-stage form of [`Constructor`].
pub type ConstructorDescriptor = Constructor<DescriptorStage>;

stage_shape! {
    /// One named constructor field.
    #[derive(Clone, Debug, Serialize, Deserialize)]
    #[serde(
        rename = "ConstructorFieldDescriptor",
        bound(
            serialize = "S::ConstructorFieldSort: Serialize",
            deserialize = "S::ConstructorFieldSort: Deserialize<'de>"
        )
    )]
    pub struct ConstructorField<S: Stage> {
        /// Rust field name.
        pub name: String => [keep],
        /// Declared or builtin field sort when known at descriptor collection time.
        #[serde(skip_serializing_if = "S::skip_constructor_field_sort")]
        pub sort: S::ConstructorFieldSort => [constructor_field_sort],
    }
}

/// Stable descriptor-stage form of [`ConstructorField`].
pub type ConstructorFieldDescriptor = ConstructorField<DescriptorStage>;

/// Explicit K sentence kind; rule ordering is never encoded here.
#[derive(Clone, Copy, Debug, Eq, Hash, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(rename_all = "snake_case")]
pub enum SentenceKind {
    /// Computational transition.
    Transition,
    /// Equational simplification or function meaning.
    Equation,
    /// A simplifier lemma imported by the simplification engine.
    Simplification,
    /// Reversible compile-time alias expansion.
    Alias,
    /// Reachability or logical claim.
    Claim,
}
