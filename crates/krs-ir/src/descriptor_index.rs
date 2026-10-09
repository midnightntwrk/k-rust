//! Borrowed descriptor lookup with typed payload access.

use std::collections::BTreeMap;
use std::error::Error;
use std::fmt;

use crate::{
    ConstructorDescriptor, Descriptor, DescriptorBundle, DescriptorCellDeclaration,
    DescriptorConfigurationRule, DescriptorContextAlias, DescriptorFixedConfiguration,
    DescriptorHeadRule, DescriptorPayload, GrammarDescriptor, ItemKind, SortDescriptor,
    StableItemId, StructuredRuleDescriptor,
};

/// A failed descriptor lookup.
#[derive(Clone, Debug, Eq, PartialEq)]
pub enum LookupError {
    /// No descriptor has the requested identity.
    Missing {
        /// Requested identity.
        id: Box<StableItemId>,
    },
    /// The descriptor has a different identity kind or sentence representation.
    WrongKind {
        /// Requested identity.
        id: Box<StableItemId>,
        /// Required declaration kind.
        expected: ItemKind,
        /// Supplied declaration kind.
        actual: ItemKind,
    },
}

impl fmt::Display for LookupError {
    fn fmt(&self, formatter: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            Self::Missing { id } => write!(formatter, "missing descriptor {id}"),
            Self::WrongKind {
                id,
                expected,
                actual,
            } => write!(
                formatter,
                "descriptor {id} has kind {actual}; expected {expected}"
            ),
        }
    }
}

impl Error for LookupError {}

/// A borrowed identity index with source-order typed iteration.
///
/// Inputs must have unique identities.
/// Lookup and [`Self::values`] use identity order; typed iterators retain input order.
#[derive(Clone, Debug)]
pub struct DescriptorIndex<'a> {
    by_id: BTreeMap<&'a StableItemId, &'a Descriptor>,
    source_order: Vec<&'a Descriptor>,
}

macro_rules! typed_accessor {
    ($name:ident, $payload:ident, $ty:ty, $kind:ident, $doc:literal) => {
        #[doc = $doc]
        ///
        /// # Errors
        ///
        /// Returns [`LookupError`] for a missing identity or a mismatched identity kind.
        pub fn $name(&self, id: &StableItemId) -> Result<&'a $ty, LookupError> {
            let descriptor = self.require(id)?;
            match descriptor.payload() {
                DescriptorPayload::$payload(payload) => Ok(payload),
                _ => Err(wrong_kind(id, ItemKind::$kind, descriptor.id().item_kind())),
            }
        }
    };
}

macro_rules! sentence_accessor {
    ($name:ident, $payload:ident, $ty:ty, $doc:literal) => {
        #[doc = $doc]
        ///
        /// # Errors
        ///
        /// Returns [`LookupError`] for a missing identity, a mismatched identity kind, or another sentence representation.
        pub fn $name(&self, id: &StableItemId) -> Result<&'a $ty, LookupError> {
            let expected = match id.item_kind() {
                kind @ (ItemKind::Rule
                | ItemKind::Equation
                | ItemKind::Simplification
                | ItemKind::Alias
                | ItemKind::Claim
                | ItemKind::Desugar
                | ItemKind::Context) => kind,
                _ => ItemKind::Rule,
            };
            let descriptor = self.require_kind(id, expected)?;
            match descriptor.payload() {
                DescriptorPayload::$payload(payload) => Ok(payload),
                _ => Err(wrong_kind(id, expected, descriptor.id().item_kind())),
            }
        }
    };
}

impl<'a> DescriptorIndex<'a> {
    /// Indexes a bundle without copying descriptors or identities.
    #[must_use]
    pub fn new(bundle: &'a DescriptorBundle) -> Self {
        Self::from_descriptors(bundle.descriptors())
    }

    /// Indexes descriptors while retaining their input order for typed iteration.
    #[must_use]
    pub fn from_descriptors(descriptors: impl IntoIterator<Item = &'a Descriptor>) -> Self {
        let source_order = descriptors.into_iter().collect::<Vec<_>>();
        let by_id = source_order
            .iter()
            .map(|descriptor| (descriptor.id(), *descriptor))
            .collect();
        Self {
            by_id,
            source_order,
        }
    }

    /// Returns a descriptor with the requested identity.
    #[must_use]
    pub fn get(&self, id: &StableItemId) -> Option<&'a Descriptor> {
        self.by_id.get(id).copied()
    }

    /// Iterates descriptors in stable identity order.
    #[must_use]
    pub fn values(&self) -> impl DoubleEndedIterator<Item = &'a Descriptor> + '_ {
        self.by_id.values().copied()
    }

    /// Iterates descriptor identities in stable identity order.
    #[must_use]
    pub fn keys(&self) -> impl DoubleEndedIterator<Item = &'a StableItemId> + '_ {
        self.by_id.keys().copied()
    }

    /// Returns a nominal cell declaration.
    ///
    /// # Errors
    ///
    /// Returns [`LookupError`] for a missing identity or a mismatched identity kind.
    pub fn cell(&self, id: &StableItemId) -> Result<&'a DescriptorCellDeclaration, LookupError> {
        self.cell_descriptor(id).map(|(_, declaration)| declaration)
    }

    /// Returns a nominal cell declaration together with its descriptor metadata.
    ///
    /// # Errors
    ///
    /// Returns [`LookupError`] for a missing identity or a mismatched identity kind.
    pub fn cell_descriptor(
        &self,
        id: &StableItemId,
    ) -> Result<(&'a Descriptor, &'a DescriptorCellDeclaration), LookupError> {
        let descriptor = self.require(id)?;
        match descriptor.payload() {
            DescriptorPayload::Cell(declaration) => Ok((descriptor, declaration)),
            _ => Err(wrong_kind(id, ItemKind::Cell, descriptor.id().item_kind())),
        }
    }

    typed_accessor!(
        sort,
        Sort,
        SortDescriptor,
        Sort,
        "Returns an open-sort declaration."
    );
    typed_accessor!(
        constructor,
        Constructor,
        ConstructorDescriptor,
        Constructor,
        "Returns a constructor declaration."
    );
    typed_accessor!(
        configuration,
        FixedConfiguration,
        DescriptorFixedConfiguration,
        Configuration,
        "Returns a fixed configuration."
    );
    typed_accessor!(
        context_alias,
        ContextAlias,
        DescriptorContextAlias,
        ContextAlias,
        "Returns a context template."
    );
    typed_accessor!(
        grammar,
        Grammar,
        GrammarDescriptor,
        Grammar,
        "Returns an object-grammar sentence."
    );
    sentence_accessor!(
        structured_rule,
        StructuredRule,
        StructuredRuleDescriptor,
        "Returns a structured relational sentence."
    );
    sentence_accessor!(
        configuration_rule,
        ConfigurationRule,
        DescriptorConfigurationRule,
        "Returns a whole-configuration sentence."
    );
    sentence_accessor!(
        head_rule,
        HeadRule,
        DescriptorHeadRule,
        "Returns a computation-head sentence."
    );

    /// Returns the fields owned by a fixed configuration or nominal cell declaration.
    ///
    /// # Errors
    ///
    /// Returns [`LookupError`] for a missing identity or an owner payload of another kind.
    pub fn cell_owner(
        &self,
        id: &StableItemId,
    ) -> Result<&'a DescriptorCellDeclaration, LookupError> {
        let descriptor = self.require(id)?;
        match descriptor.payload() {
            DescriptorPayload::FixedConfiguration(configuration) => Ok(&configuration.declaration),
            DescriptorPayload::Cell(declaration) => Ok(declaration),
            _ => Err(wrong_kind(id, ItemKind::Cell, descriptor.id().item_kind())),
        }
    }

    /// Iterates constructor descriptors and payloads in input order.
    pub fn constructors(
        &self,
    ) -> impl Iterator<Item = (&'a Descriptor, &'a ConstructorDescriptor)> + '_ {
        self.source_order.iter().filter_map(|descriptor| {
            if let DescriptorPayload::Constructor(constructor) = descriptor.payload() {
                Some((*descriptor, constructor))
            } else {
                None
            }
        })
    }

    /// Iterates head-rule descriptors and payloads in input order.
    pub fn head_rules(
        &self,
    ) -> impl Iterator<Item = (&'a Descriptor, &'a DescriptorHeadRule)> + '_ {
        self.source_order.iter().filter_map(|descriptor| {
            if let DescriptorPayload::HeadRule(rule) = descriptor.payload() {
                Some((*descriptor, rule.as_ref()))
            } else {
                None
            }
        })
    }

    fn require(&self, id: &StableItemId) -> Result<&'a Descriptor, LookupError> {
        self.get(id).ok_or_else(|| LookupError::Missing {
            id: Box::new(id.clone()),
        })
    }

    fn require_kind(
        &self,
        id: &StableItemId,
        expected: ItemKind,
    ) -> Result<&'a Descriptor, LookupError> {
        let descriptor = self.require(id)?;
        let actual = descriptor.id().item_kind();
        if actual != expected {
            return Err(wrong_kind(id, expected, actual));
        }
        Ok(descriptor)
    }
}

fn wrong_kind(id: &StableItemId, expected: ItemKind, actual: ItemKind) -> LookupError {
    LookupError::WrongKind {
        id: Box::new(id.clone()),
        expected,
        actual,
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::testing::{authored, item};
    use crate::{
        BuiltinSort, CellWrapper, ConstructorFieldDescriptor, DescriptorCellField,
        DescriptorCellIdentity, DescriptorCellReference, DescriptorConfigurationInitializer,
        DescriptorConfigurationRoot, DescriptorInitializerCell, DescriptorNodeOrigin,
        DescriptorProvenance, DescriptorSortRef, DescriptorSortReference, DescriptorTerm,
        ProtocolCellContent, ProtocolHeadRuleResult, ProtocolInitializerCellContent,
        ProtocolInitializerStateTerm, ProtocolMap, ProtocolMapBody, ProvenanceKey, ProvenanceRole,
        SentenceKind,
    };

    fn key() -> ProvenanceKey {
        ProvenanceKey::new(ProvenanceRole::ConfigurationDeclaration, 0)
    }

    fn descriptor(name: &str, kind: ItemKind, payload: DescriptorPayload) -> Descriptor {
        let id = item("lookup", name, kind);
        let keys = match &payload {
            DescriptorPayload::FixedConfiguration(configuration) => {
                configuration.expected_provenance_keys(&id).unwrap()
            }
            DescriptorPayload::Cell(declaration) => {
                declaration.expected_provenance_keys(&id).unwrap()
            }
            _ => [key()].into(),
        };
        crate::testing::descriptor(
            id,
            BTreeMap::new(),
            DescriptorProvenance::new(
                key(),
                keys.into_iter()
                    .map(|key| DescriptorNodeOrigin::new(key, authored(0, 3)))
                    .collect(),
            )
            .unwrap(),
            payload,
        )
    }

    fn constructor(name: &str) -> Descriptor {
        descriptor(
            name,
            ItemKind::Constructor,
            DescriptorPayload::Constructor(ConstructorDescriptor {
                parameters: Vec::new(),
                sort: DescriptorSortRef::Declared(item("lookup", "Sort", ItemKind::Sort)),
                fields: vec![ConstructorFieldDescriptor {
                    name: "field".into(),
                    sort: Some(DescriptorSortRef::Declared(item(
                        "lookup",
                        "Sort",
                        ItemKind::Sort,
                    ))),
                }],
            }),
        )
    }

    fn head_rule(name: &str) -> Descriptor {
        let configuration = item("lookup", "Configuration", ItemKind::Configuration);
        descriptor(
            name,
            ItemKind::Rule,
            DescriptorPayload::HeadRule(Box::new(DescriptorHeadRule {
                sentence_kind: SentenceKind::Transition,
                label: None,
                priority: None,
                nondet: None,
                pattern_key: key(),
                result_key: key(),
                head_sort: None,
                configuration: configuration.clone(),
                computation_cell: Some(DescriptorCellReference {
                    key: key(),
                    cell: DescriptorCellIdentity {
                        owner: configuration,
                        field: "k".into(),
                    },
                }),
                bindings: Vec::new(),
                head: Some(crate::ProtocolHeadRuleHead {
                    subject: DescriptorTerm::Variable {
                        key: key(),
                        path_key: key(),
                        name: "head".into(),
                    },
                    result: ProtocolHeadRuleResult::Erase,
                }),
                requires: None,
                extras: Vec::new(),
                existentials: Vec::new(),
                ensures: None,
                fresh: Vec::new(),
                evaluation: None,
            })),
        )
    }

    #[test]
    fn typed_lookup_borrows_the_payload() {
        let descriptor = constructor("Constructor");
        let bundle = DescriptorBundle::new(vec![descriptor]).unwrap();
        let index = DescriptorIndex::new(&bundle);
        let descriptor = &bundle.descriptors()[0];
        let DescriptorPayload::Constructor(payload) = descriptor.payload() else {
            panic!("fixture must be a constructor")
        };
        assert!(std::ptr::eq(
            index.get(descriptor.id()).unwrap(),
            descriptor
        ));
        assert!(std::ptr::eq(
            index.constructor(descriptor.id()).unwrap(),
            payload
        ));
    }

    #[test]
    fn lookup_distinguishes_missing_identity_and_wrong_kind() {
        let descriptor = constructor("Constructor");
        let index = DescriptorIndex::from_descriptors([&descriptor]);
        let missing = item("lookup", "Missing", ItemKind::Sort);
        assert_eq!(
            index.sort(&missing).unwrap_err(),
            LookupError::Missing {
                id: Box::new(missing)
            }
        );
        assert_eq!(
            index.sort(descriptor.id()).unwrap_err(),
            wrong_kind(descriptor.id(), ItemKind::Sort, ItemKind::Constructor)
        );
    }

    #[test]
    fn constructor_and_deserialization_reject_payload_kind_mismatch() {
        let descriptor = constructor("Constructor");
        let mut inputs = crate::testing::DescriptorInputs::from(descriptor);
        inputs.payload = DescriptorPayload::Sort(SortDescriptor::default());
        let error = crate::DescriptorError::WrongKind {
            id: Box::new(inputs.id.clone()),
            expected: ItemKind::Sort,
            actual: ItemKind::Constructor,
        };
        assert_eq!(inputs.build(), Err(error.clone()));
        let wire = serde_json::to_value(&inputs).unwrap();
        let decoded = serde_json::from_value::<Descriptor>(wire).unwrap_err();
        assert!(decoded.to_string().contains(&error.to_string()));
    }

    #[test]
    fn typed_iterators_retain_input_order_while_values_use_identity_order() {
        let descriptors = [
            constructor("Z"),
            head_rule("Y"),
            constructor("B"),
            head_rule("A"),
        ];
        let index = DescriptorIndex::from_descriptors(&descriptors);
        assert_eq!(
            index
                .values()
                .map(|descriptor| descriptor.id().item_name())
                .collect::<Vec<_>>(),
            ["A", "B", "Y", "Z"]
        );
        assert_eq!(
            index
                .constructors()
                .map(|(descriptor, _)| descriptor.id().item_name())
                .collect::<Vec<_>>(),
            ["Z", "B"]
        );
        assert_eq!(
            index
                .head_rules()
                .map(|(descriptor, _)| descriptor.id().item_name())
                .collect::<Vec<_>>(),
            ["Y", "A"]
        );
    }

    fn cell_declaration(owner: StableItemId) -> DescriptorCellDeclaration {
        let role = |role| ProvenanceKey::new(role, 0);
        DescriptorCellDeclaration {
            key: key(),
            fields: vec![DescriptorCellField {
                reference: DescriptorCellReference {
                    key: role(ProvenanceRole::ConfigurationField),
                    cell: DescriptorCellIdentity {
                        owner,
                        field: "env".into(),
                    },
                },
                rust_field: "env".into(),
                emitted_name: None,
                color: None,
                multiplicity: None,
                cell_type: None,
                stream: None,
                exit: None,
                initial: None,
                content: ProtocolCellContent::Leaf {
                    wrapper_key: role(ProvenanceRole::ConfigurationCellWrapper),
                    wrapper: CellWrapper::Cell,
                    sort: DescriptorSortReference {
                        key: role(ProvenanceRole::ConfigurationCellContent),
                        sort: DescriptorSortRef::Builtin(BuiltinSort::Map),
                    },
                    arguments: Vec::new(),
                },
            }],
        }
    }

    #[test]
    fn cell_owner_accepts_both_owner_payloads_and_retains_mismatch_kind() {
        let declaration = cell_declaration(item("lookup", "Cell", ItemKind::Cell));
        let cell = descriptor(
            "Cell",
            ItemKind::Cell,
            DescriptorPayload::Cell(Box::new(declaration.clone())),
        );
        let configuration_declaration =
            cell_declaration(item("lookup", "Configuration", ItemKind::Configuration));
        let configuration = descriptor(
            "Configuration",
            ItemKind::Configuration,
            DescriptorPayload::FixedConfiguration(Box::new(DescriptorFixedConfiguration {
                root: DescriptorConfigurationRoot::GeneratedTop,
                declaration: configuration_declaration.clone(),
                initializer: DescriptorConfigurationInitializer {
                    key: ProvenanceKey::new(ProvenanceRole::InitializerDeclaration, 0),
                    owner_key: ProvenanceKey::new(ProvenanceRole::InitializerResultType, 0),
                    owner: item("lookup", "Configuration", ItemKind::Configuration),
                    variables: Vec::new(),
                    body_key: ProvenanceKey::new(ProvenanceRole::InitializerBody, 0),
                    cells: vec![DescriptorInitializerCell {
                        key: ProvenanceKey::new(ProvenanceRole::InitializerCell, 0),
                        field: DescriptorCellReference {
                            key: ProvenanceKey::new(ProvenanceRole::InitializerField, 0),
                            cell: configuration_declaration.fields[0].reference.cell.clone(),
                        },
                        content: ProtocolInitializerCellContent::Leaf {
                            constructor_key: ProvenanceKey::new(
                                ProvenanceRole::InitializerCellConstructor,
                                0,
                            ),
                            wrapper: CellWrapper::Cell,
                            value: ProtocolInitializerStateTerm::Map(ProtocolMap {
                                payload_key: None,
                                body: ProtocolMapBody::Empty {
                                    explicit_dot: false,
                                },
                            }),
                        },
                    }],
                },
            })),
        );
        let other = constructor("Constructor");
        let index = DescriptorIndex::from_descriptors([&cell, &configuration, &other]);
        assert_eq!(index.cell_owner(cell.id()).unwrap(), &declaration);
        assert_eq!(
            index.cell_owner(configuration.id()).unwrap(),
            &configuration_declaration
        );
        assert_eq!(
            index.cell_owner(other.id()).unwrap_err(),
            wrong_kind(other.id(), ItemKind::Cell, ItemKind::Constructor)
        );
    }
}
