//! Serializable collector output.

use std::collections::{BTreeMap, BTreeSet};
use std::error::Error;
use std::fmt;

use serde::{Deserialize, Deserializer, Serialize};

use crate::host::{
    ConfigurationDescriptorError, DuplicateReferenceKey, RuleBindingError,
    validate_configuration_shape, validate_rule_bindings, validate_unique_reference_keys,
};
use crate::{
    BuiltinSort, DescriptorCellDeclaration, DescriptorConfigurationRule, DescriptorContextAlias,
    DescriptorFixedConfiguration, DescriptorSortRef, ExplicitSymbol, GrammarDescriptor, ItemKind,
    OriginStack, ProtocolV6ShapeError, ProtocolV7ShapeError, ProtocolVersion, ProvenanceKey,
    RustVisibility, StableItemId, StructuredRuleDescriptor,
};

/// Deterministic, serializable output of one host collector execution.
#[derive(Clone, Debug, Eq, PartialEq, Serialize)]
pub struct DescriptorBundle {
    /// Schema and canonical-encoding version.
    protocol_version: ProtocolVersion,
    /// Collected descriptors. Canonical serialization orders these by ID.
    pub descriptors: Vec<Descriptor>,
    /// Exact Rust API metadata for every collected descriptor.
    pub declarations: Vec<DescriptorDeclaration>,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct DescriptorBundleWire {
    protocol_version: ProtocolVersion,
    descriptors: Vec<Descriptor>,
    declarations: Vec<DescriptorDeclaration>,
}

impl<'de> Deserialize<'de> for DescriptorBundle {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = DescriptorBundleWire::deserialize(deserializer)?;
        if wire.protocol_version != ProtocolVersion::CURRENT {
            return Err(serde::de::Error::custom(format_args!(
                "unsupported descriptor protocol {}; expected {}",
                wire.protocol_version.0,
                ProtocolVersion::CURRENT.0
            )));
        }
        for descriptor in &wire.descriptors {
            descriptor
                .validate_configuration_contract()
                .map_err(serde::de::Error::custom)?;
            descriptor
                .validate_v6_contract()
                .map_err(serde::de::Error::custom)?;
            descriptor
                .validate_v7_contract()
                .map_err(serde::de::Error::custom)?;
        }
        validate_declarations(&wire.descriptors, &wire.declarations)
            .map_err(serde::de::Error::custom)?;
        Ok(Self {
            protocol_version: wire.protocol_version,
            descriptors: wire.descriptors,
            declarations: wire.declarations,
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
            protocol_version: ProtocolVersion::CURRENT,
            descriptors,
            declarations,
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
            protocol_version: ProtocolVersion::CURRENT,
            descriptors,
            declarations,
        })
    }

    /// Creates an empty bundle using the current protocol.
    #[must_use]
    pub fn empty() -> Self {
        Self::new(Vec::new())
    }

    /// Returns the serialized collector protocol version.
    #[must_use]
    pub const fn protocol_version(&self) -> ProtocolVersion {
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
    /// Descriptor order and parent-sort order are normalized on a clone, so
    /// this method never gives insertion order serialized meaning.
    ///
    /// # Errors
    ///
    /// Returns an error if this protocol's serde data model cannot be encoded
    /// as JSON. Current descriptor variants contain no fallible JSON values.
    pub fn to_canonical_json(&self) -> serde_json::Result<String> {
        let mut canonical = self.clone();
        canonical.canonicalize();
        let mut json = serde_json::to_string_pretty(&canonical)?;
        json.push('\n');
        Ok(json)
    }

    fn canonicalize(&mut self) {
        for descriptor in &mut self.descriptors {
            descriptor.canonicalize();
        }
        self.descriptors.sort();
        self.declarations.sort();
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
            Self::Missing(id) => write!(formatter, "missing declaration metadata for {id:?}"),
            Self::Extra(id) => write!(formatter, "declaration metadata names unknown {id:?}"),
            Self::Duplicate(id) => write!(formatter, "duplicate declaration metadata for {id:?}"),
            Self::MissingSymbolOrigin(id) => {
                write!(
                    formatter,
                    "explicit symbol metadata for {id:?} has no exact origin"
                )
            }
            Self::UnexpectedSymbolOrigin(id) => write!(
                formatter,
                "stable-symbol origin for {id:?} has no explicit symbol metadata"
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
        let has_symbol_origin = descriptor
            .provenance
            .origins()
            .iter()
            .any(|origin| origin.key.role() == "stable_symbol" && origin.key.ordinal() == 0);
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
    /// Returns the primary declaration's authored-to-descriptor provenance.
    #[must_use]
    pub fn origin(&self) -> &OriginStack {
        self.provenance.primary_origin()
    }

    /// Validates configuration item ownership and reference-origin joins.
    ///
    /// Other descriptor variants have no additional v5 checks here.
    ///
    /// # Errors
    ///
    /// Returns [`ConfigurationDescriptorError`] when a configuration payload
    /// has the wrong outer item kind, invalid fixed data, or a semantic
    /// reference without an exact parser-keyed origin.
    pub fn validate_configuration_contract(&self) -> Result<(), ConfigurationDescriptorError> {
        let DescriptorPayload::Configuration(configuration) = &self.payload else {
            return Ok(());
        };
        if self.id.item_kind() != ItemKind::Configuration {
            return Err(ConfigurationDescriptorError::ConfigurationItemKindMismatch(
                self.id.item_kind(),
            ));
        }
        configuration.validate()?;
        let references = configuration
            .main_variable
            .iter()
            .map(|variable| &variable.sort)
            .chain(configuration.initializer.references.iter());
        for reference in references {
            if self.provenance.origin_for(&reference.key).is_none() {
                return Err(
                    ConfigurationDescriptorError::MissingInitializerReferenceOrigin(
                        reference.key.clone(),
                    ),
                );
            }
        }
        Ok(())
    }

    /// Validates typed grammar or structured-rule protocol-v6 extensions.
    ///
    /// # Errors
    ///
    /// Returns [`ProtocolV6ShapeError`] for invalid ownership, shape,
    /// references, or parser keys absent from this descriptor's provenance.
    pub fn validate_v6_contract(&self) -> Result<(), ProtocolV6ShapeError> {
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
            | DescriptorPayload::Configuration(_)
            | DescriptorPayload::Rule(_)
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
            .filter(|origin| origin.key.role() != "stable_symbol")
            .map(|origin| origin.key.clone())
            .collect::<BTreeSet<_>>();
        if let Some(missing) = expected.difference(&actual).next() {
            return Err(ProtocolV6ShapeError::MissingProvenance(missing.clone()));
        }
        if let Some(unexpected) = actual.difference(&expected).next() {
            return Err(ProtocolV6ShapeError::ExtraProvenance(unexpected.clone()));
        }
        let Some(expected_primary) = expected_primary else {
            return Err(ProtocolV6ShapeError::EmptyCollection(
                "required v6 primary provenance key",
            ));
        };
        if self.provenance.primary_key() != &expected_primary {
            return Err(ProtocolV6ShapeError::UnexpectedProvenance {
                expected: expected_primary,
                actual: self.provenance.primary_key().clone(),
            });
        }
        Ok(())
    }

    /// Validates protocol-v7 fixed configurations, nominal cells, and
    /// simultaneous configuration rules against exact closed provenance.
    ///
    /// # Errors
    ///
    /// Returns [`ProtocolV7ShapeError`] for wrong ownership, invalid typed
    /// state, frame/binding errors, or missing/extra parser keys.
    pub fn validate_v7_contract(&self) -> Result<(), ProtocolV7ShapeError> {
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
            | DescriptorPayload::Configuration(_)
            | DescriptorPayload::Rule(_)
            | DescriptorPayload::Grammar(_)
            | DescriptorPayload::StructuredRule(_) => Ok(()),
        }
    }

    fn canonicalize(&mut self) {
        self.provenance.canonicalize();
        match &mut self.payload {
            DescriptorPayload::Sort(sort) => {
                sort.parents.sort();
                sort.parents.dedup();
            }
            DescriptorPayload::Rule(rule) => rule.references.sort(),
            DescriptorPayload::Configuration(configuration) => {
                configuration.initializer.references.sort();
            }
            DescriptorPayload::Constructor(_)
            | DescriptorPayload::Grammar(_)
            | DescriptorPayload::StructuredRule(_)
            | DescriptorPayload::FixedConfiguration(_)
            | DescriptorPayload::Cell(_)
            | DescriptorPayload::ConfigurationRule(_)
            | DescriptorPayload::HeadRule(_)
            | DescriptorPayload::ContextAlias(_) => {}
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
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct DescriptorProvenance {
    primary_key: ProvenanceKey,
    origins: Vec<DescriptorNodeOrigin>,
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
            origins,
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

    fn canonicalize(&mut self) {
        self.origins.sort_by(|left, right| left.key.cmp(&right.key));
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

/// Minimal serializable declaration variants.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(
    tag = "descriptor_kind",
    content = "descriptor",
    rename_all = "snake_case",
    deny_unknown_fields
)]
pub enum DescriptorPayload {
    /// Open-sort declaration.
    Sort(SortDescriptor),
    /// Constructor declaration.
    Constructor(ConstructorDescriptor),
    /// Fixed configuration and its paired initializer.
    Configuration(ConfigurationDescriptor),
    /// Relational sentence declaration.
    Rule(RuleDescriptor),
    /// Typed after-the-fact object-grammar sentence.
    Grammar(Box<GrammarDescriptor>),
    /// Fully structured relational sentence using typed term references.
    StructuredRule(Box<StructuredRuleDescriptor>),
    /// Protocol-v7 complete fixed configuration and initializer.
    FixedConfiguration(Box<DescriptorFixedConfiguration>),
    /// Protocol-v7 nominal nested fixed-cell declaration.
    Cell(Box<DescriptorCellDeclaration>),
    /// Protocol-v7 simultaneous whole-configuration rule.
    ConfigurationRule(Box<DescriptorConfigurationRule>),
    /// Collector-completed bare-sort computation-head rule.
    HeadRule(Box<crate::DescriptorHeadRule>),
    /// One-sided reusable fixed-configuration context template.
    ContextAlias(Box<DescriptorContextAlias>),
}

/// Resolved open-sort payload.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct SortDescriptor {
    /// Direct super-sorts. This is a set in canonical output.
    pub parents: Vec<StableItemId>,
}

/// Resolved constructor payload.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct ConstructorDescriptor {
    /// Sort directly containing the constructor.
    pub sort: DescriptorSortRef,
    /// Checked authored syntax template.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub syntax: Option<String>,
    /// Fields in authored constructor order.
    pub fields: Vec<ConstructorFieldDescriptor>,
}

/// One named constructor field.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct ConstructorFieldDescriptor {
    /// Rust field name.
    pub name: String,
    /// Declared or builtin field sort when known at descriptor collection time.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub sort: Option<crate::DescriptorSortRef>,
}

/// The sole fixed computation cell represented without Rust wrapper paths.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConfigurationCellDescriptor {
    /// Exact authored field name (`k`).
    pub name: String,
    /// Intrinsic content sort, always builtin `KSequence` in M2.
    pub content_sort: BuiltinSort,
}

/// Stable combined configuration/initializer payload.
///
/// Its enclosing descriptor owns the only [`StableItemId`]. The initializer
/// receives a semantic/generated identity during lowering and is never an
/// independently registered Rust declaration.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize)]
pub struct ConfigurationDescriptor {
    /// Authored root-cell name used for configuration selection and naming.
    pub root: String,
    /// The fixed authored computation cell.
    pub cell: ConfigurationCellDescriptor,
    /// Zero or one explicitly main configuration variable.
    #[serde(skip_serializing_if = "Option::is_none")]
    pub main_variable: Option<ConfigurationVariableDescriptor>,
    /// Exactly one paired declarative initializer.
    pub initializer: ConfigurationInitializerDescriptor,
}

#[derive(Deserialize)]
#[serde(deny_unknown_fields)]
struct ConfigurationDescriptorWire {
    root: String,
    cell: ConfigurationCellDescriptor,
    main_variable: Option<ConfigurationVariableDescriptor>,
    initializer: ConfigurationInitializerDescriptor,
}

impl TryFrom<ConfigurationDescriptorWire> for ConfigurationDescriptor {
    type Error = ConfigurationDescriptorError;

    fn try_from(wire: ConfigurationDescriptorWire) -> Result<Self, Self::Error> {
        let descriptor = Self {
            root: wire.root,
            cell: wire.cell,
            main_variable: wire.main_variable,
            initializer: wire.initializer,
        };
        descriptor.validate()?;
        Ok(descriptor)
    }
}

impl<'de> Deserialize<'de> for ConfigurationDescriptor {
    fn deserialize<D>(deserializer: D) -> Result<Self, D::Error>
    where
        D: Deserializer<'de>,
    {
        let wire = ConfigurationDescriptorWire::deserialize(deserializer)?;
        Self::try_from(wire).map_err(serde::de::Error::custom)
    }
}

impl ConfigurationDescriptor {
    /// Validates the closed M2 shape, reference keys, and stable target kinds.
    ///
    /// The shared syntax parser remains responsible for reparsing `term` and
    /// proving that its complete path set matches `references`; the protocol
    /// deliberately does not define a second term AST.
    ///
    /// # Errors
    ///
    /// Returns [`ConfigurationDescriptorError`] for malformed fixed data,
    /// duplicate/wrong parser roles, or a resolved target of the wrong kind.
    pub fn validate(&self) -> Result<(), ConfigurationDescriptorError> {
        validate_configuration_shape(
            &self.root,
            &self.cell,
            self.main_variable.as_ref().map(|variable| {
                (
                    variable.binding.as_str(),
                    variable.external_name.as_str(),
                    &variable.sort.key,
                )
            }),
            &self.initializer.name,
            &self.initializer.term,
            self.initializer
                .references
                .iter()
                .map(|reference| &reference.key),
        )?;
        if let Some(variable) = &self.main_variable {
            validate_configuration_target(&variable.sort, ItemKind::Sort)?;
        }
        for reference in &self.initializer.references {
            validate_configuration_target(reference, ItemKind::Constructor)?;
        }
        Ok(())
    }
}

/// Optional main configuration-variable metadata.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConfigurationVariableDescriptor {
    /// Authored Rust parameter binding.
    pub binding: String,
    /// External K configuration-variable name.
    pub external_name: String,
    /// Parser-keyed resolved declared sort.
    pub sort: DescriptorReference,
}

/// Stable paired initializer syntax and semantic references.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
#[serde(deny_unknown_fields)]
pub struct ConfigurationInitializerDescriptor {
    /// Fixed authored associated-method name (`init`).
    pub name: String,
    /// Deterministic single-item spelling for the existing shared term parser.
    pub term: String,
    /// Parser-keyed resolved named term constructors.
    pub references: Vec<DescriptorReference>,
}

fn validate_configuration_target(
    reference: &DescriptorReference,
    expected: ItemKind,
) -> Result<(), ConfigurationDescriptorError> {
    let actual = reference.target.item_kind();
    if actual == expected {
        Ok(())
    } else {
        Err(ConfigurationDescriptorError::ReferenceKindMismatch {
            key: reference.key.clone(),
            expected,
            actual,
        })
    }
}

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

/// One collector-resolved Rust target keyed to its parser-owned AST position.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct DescriptorReference {
    /// Parser-owned semantic role and AST-order ordinal.
    pub key: ProvenanceKey,
    /// Stable item identity resolved from the host process's Rust type key.
    pub target: StableItemId,
}

impl DescriptorReference {
    /// Associates a parser-owned key with one stable target.
    #[must_use]
    pub const fn new(key: ProvenanceKey, target: StableItemId) -> Self {
        Self { key, target }
    }
}

/// Minimal resolved rule/equation/claim payload.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct RuleDescriptor {
    /// Explicit sentence kind.
    pub sentence_kind: SentenceKind,
    /// Parameters in authored order.
    pub parameters: Vec<RuleParameterDescriptor>,
    /// Result sort resolved by rustc and the collector.
    pub result_sort: StableItemId,
    /// Explicit constructor and type targets from the authored rule.
    pub references: Vec<DescriptorReference>,
    /// Deterministic explicit-surface left-hand payload.
    pub lhs: String,
    /// Deterministic explicit-surface right-hand payload.
    pub rhs: String,
}

impl RuleDescriptor {
    /// Validates the collector's one-target-per-parser-node invariant.
    ///
    /// # Errors
    ///
    /// Returns [`DuplicateReferenceKey`] for the first repeated role/ordinal.
    pub fn validate_reference_keys(&self) -> Result<(), DuplicateReferenceKey> {
        validate_unique_reference_keys(self.references.iter().map(|reference| &reference.key))
    }

    /// Validates all binding names without changing authored preorder.
    ///
    /// # Errors
    ///
    /// Returns [`RuleBindingError`] for a blank or repeated binding.
    pub fn validate_bindings(&self) -> Result<(), RuleBindingError> {
        validate_rule_bindings(
            self.parameters
                .iter()
                .map(|parameter| parameter.bindings.as_slice()),
        )
    }
}

/// One resolved rule binder and pattern.
#[derive(Clone, Debug, Eq, Ord, PartialEq, PartialOrd, Serialize, Deserialize)]
pub struct RuleParameterDescriptor {
    /// Binder names in deterministic authored pattern preorder; may be empty.
    pub bindings: Vec<String>,
    /// Sort of the parameter.
    pub sort: StableItemId,
    /// Deterministic reference-surface pattern payload.
    pub pattern: String,
}

impl RuleParameterDescriptor {
    /// Validates this parameter's bindings without sorting them.
    ///
    /// # Errors
    ///
    /// Returns [`RuleBindingError`] for a blank or repeated binding.
    pub fn validate_bindings(&self) -> Result<(), RuleBindingError> {
        validate_rule_bindings(std::iter::once(self.bindings.as_slice()))
    }
}
