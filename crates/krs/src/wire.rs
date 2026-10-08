//! Runtime substitution of indexed, static host payloads.

use std::convert::Infallible;

use krs_ir::wire::{
    ItemSlot, TypeSlot, WireApplicationReference, WireCellDeclarationReference, WireCellReference,
    WireConfigurationReference, WireContextAliasReference, WireHeadRuleCellReference, WirePayload,
    WireSortReference, WireTypeReference,
};
use krs_ir::{
    HostApplicationReference, HostApplicationTarget, HostCellDeclarationReference,
    HostCellIdentity, HostCellReference, HostConfigurationReference, HostContextAliasReference,
    HostDescriptorPayload, HostEnumVariantReference, HostHeadRuleCellReference, HostItemId,
    HostSortReference, HostStage, HostTypeKey, HostTypeReference, RefMap, WireStage,
};

/// Rust-resolved application identity inserted into a static descriptor payload.
#[doc(hidden)]
#[derive(Clone, Debug)]
pub enum __KrsTargetSlot {
    /// Build-local nominal Rust type identity.
    Nominal(HostTypeKey),
    /// Exact owner and generated marker for a Rust enum variant.
    Variant {
        owner: HostTypeKey,
        marker: HostTypeKey,
    },
    /// Application identity, including an inferred readable-rule head.
    Target(HostApplicationTarget),
}

/// Independently indexed Rust-resolved references for a static descriptor payload.
#[doc(hidden)]
#[derive(Clone, Copy, Debug, Default)]
pub struct __KrsSlots<'a> {
    /// Build-local Rust type identities.
    pub types: &'a [HostTypeKey],
    /// Macro-context identities for referenced items.
    pub items: &'a [HostItemId],
    /// Application identities.
    pub targets: &'a [__KrsTargetSlot],
}

/// Decode one static payload and insert the factory's Rust-resolved slots.
#[doc(hidden)]
#[inline(never)]
#[track_caller]
#[must_use]
pub fn __krs_host_payload(wire: &str, slots: __KrsSlots<'_>) -> HostDescriptorPayload {
    let payload: WirePayload = krs_ir::json::from_slice(wire.as_bytes())
        .unwrap_or_else(|error| panic!("KRS generated rule wire is malformed: {error}"));
    let map = &mut Decoder { slots };
    match payload {
        WirePayload::Sort(value) => {
            HostDescriptorPayload::Sort(value.try_map_refs(map).unwrap().into())
        }
        WirePayload::Constructor(value) => {
            HostDescriptorPayload::Constructor(value.try_map_refs(map).unwrap().into())
        }
        WirePayload::Grammar(value) => {
            HostDescriptorPayload::Grammar(Box::new(value.try_map_refs(map).unwrap()))
        }
        WirePayload::StructuredRule(value) => {
            HostDescriptorPayload::StructuredRule(Box::new(value.try_map_refs(map).unwrap()))
        }
        WirePayload::FixedConfiguration(value) => {
            HostDescriptorPayload::FixedConfiguration(Box::new(value.try_map_refs(map).unwrap()))
        }
        WirePayload::Cell(value) => HostDescriptorPayload::Cell(Box::new(
            krs_ir::transport::configuration::map_declaration(*value, map).unwrap(),
        )),
        WirePayload::ConfigurationRule(value) => {
            HostDescriptorPayload::ConfigurationRule(Box::new(value.try_map_refs(map).unwrap()))
        }
        WirePayload::HeadRule(value) => {
            HostDescriptorPayload::HeadRule(Box::new(value.try_map_refs(map).unwrap()))
        }
        WirePayload::ContextAlias(value) => {
            HostDescriptorPayload::ContextAlias(Box::new(value.try_map_refs(map).unwrap()))
        }
    }
}

impl __KrsSlots<'_> {
    /// Decode paired configuration data with independently indexed declaration and initializer slots.
    #[doc(hidden)]
    #[inline(never)]
    #[track_caller]
    #[must_use]
    pub fn __krs_fixed_configuration(
        self,
        declaration_wire: &str,
        initializer_wire: &str,
        initializer_slots: Self,
    ) -> HostDescriptorPayload {
        use krs_ir::transport::configuration::{map_declaration, map_initializer};
        use krs_ir::wire::{WireCellDeclaration, WireConfigurationInitializer};

        let (root, declaration): (krs_ir::DescriptorConfigurationRoot, WireCellDeclaration) =
            krs_ir::json::from_slice(declaration_wire.as_bytes()).unwrap_or_else(|error| {
                panic!("KRS generated configuration wire is malformed: {error}")
            });
        let initializer: WireConfigurationInitializer =
            krs_ir::json::from_slice(initializer_wire.as_bytes()).unwrap_or_else(|error| {
                panic!("KRS generated initializer wire is malformed: {error}")
            });
        HostDescriptorPayload::FixedConfiguration(Box::new(krs_ir::HostFixedConfiguration {
            root,
            declaration: map_declaration(declaration, &mut Decoder { slots: self }).unwrap(),
            initializer: map_initializer(
                initializer,
                &mut Decoder {
                    slots: initializer_slots,
                },
            )
            .unwrap(),
        }))
    }
}

struct Decoder<'a> {
    slots: __KrsSlots<'a>,
}

impl Decoder<'_> {
    fn type_key(&self, slot: TypeSlot) -> HostTypeKey {
        *self.slots.types.get(slot.0).unwrap_or_else(|| {
            panic!(
                "KRS generated rule wire has an invalid type slot {}",
                slot.0
            )
        })
    }

    fn type_reference(&self, wire: WireTypeReference) -> HostTypeReference {
        HostTypeReference {
            key: self.type_key(wire.slot),
            authored_path: wire.authored_path,
        }
    }

    fn target(&self, wire: WireApplicationReference) -> HostApplicationReference {
        let target = match self.slots.targets.get(wire.target.0).unwrap_or_else(|| {
            panic!(
                "KRS generated rule wire has an invalid target slot {}",
                wire.target.0
            )
        }) {
            __KrsTargetSlot::Target(target) => target.clone(),
            __KrsTargetSlot::Nominal(key) => HostApplicationTarget::Nominal(HostTypeReference {
                key: *key,
                authored_path: wire.authored_path.clone(),
            }),
            __KrsTargetSlot::Variant { owner, marker } => {
                let (owner_path, _) = wire.authored_path.rsplit_once("::").unwrap_or_else(|| {
                    panic!("KRS generated rule wire has an unqualified enum variant path")
                });
                HostApplicationTarget::EnumVariant(
                    HostEnumVariantReference::new(
                        HostTypeReference {
                            key: *owner,
                            authored_path: owner_path.trim().to_owned(),
                        },
                        *marker,
                        wire.authored_path.clone(),
                    )
                    .expect("KRS generated rule wire has an invalid enum variant path"),
                )
            }
        };
        assert!(
            target.authored_path() == wire.authored_path
                || target
                    .authored_path()
                    .strip_suffix(&wire.authored_path)
                    .is_some_and(|prefix| prefix.ends_with("::")),
            "KRS generated rule wire has a mismatched authored application path"
        );
        HostApplicationReference {
            key: wire.key,
            target,
        }
    }
}

impl RefMap<WireStage, HostStage> for Decoder<'_> {
    type Error = Infallible;

    fn sort(&mut self, wire: WireSortReference) -> Result<HostSortReference, Self::Error> {
        Ok(HostSortReference {
            key: wire.key,
            target: self.type_reference(wire.target),
        })
    }

    fn application(
        &mut self,
        wire: WireApplicationReference,
    ) -> Result<HostApplicationReference, Self::Error> {
        Ok(self.target(wire))
    }

    fn nominal(&mut self, wire: WireTypeReference) -> Result<HostTypeReference, Self::Error> {
        Ok(self.type_reference(wire))
    }

    fn context_alias(
        &mut self,
        wire: WireContextAliasReference,
    ) -> Result<HostContextAliasReference, Self::Error> {
        Ok(HostContextAliasReference {
            key: wire.key,
            alias: self.item(wire.slot)?,
        })
    }

    fn configuration(
        &mut self,
        wire: WireConfigurationReference,
    ) -> Result<HostConfigurationReference, Self::Error> {
        Ok(HostConfigurationReference {
            key: wire.key,
            configuration: self.type_reference(wire.configuration),
        })
    }

    fn cell(&mut self, wire: WireCellReference) -> Result<HostCellReference, Self::Error> {
        Ok(HostCellReference {
            key: wire.key,
            cell: HostCellIdentity {
                owner: self.type_key(wire.cell.owner),
                field: self.type_key(wire.cell.field),
            },
        })
    }

    fn head_rule_cell(
        &mut self,
        wire: WireHeadRuleCellReference,
    ) -> Result<HostHeadRuleCellReference, Self::Error> {
        Ok(HostHeadRuleCellReference {
            key: wire.key,
            name: wire.name,
        })
    }

    fn item(&mut self, slot: ItemSlot) -> Result<HostItemId, Self::Error> {
        Ok(self
            .slots
            .items
            .get(slot.0)
            .unwrap_or_else(|| panic!("KRS generated wire has an invalid item slot {}", slot.0))
            .clone())
    }

    fn cell_declaration(
        &mut self,
        wire: WireCellDeclarationReference,
    ) -> Result<HostCellDeclarationReference, Self::Error> {
        Ok(HostCellDeclarationReference {
            key: wire.key,
            declaration: self.type_reference(wire.declaration),
        })
    }

    fn initializer_owner(&mut self, wire: WireTypeReference) -> Result<HostTypeKey, Self::Error> {
        Ok(self.type_reference(wire).key)
    }

    fn parent(&mut self, wire: WireTypeReference) -> Result<HostTypeReference, Self::Error> {
        self.nominal(wire)
    }

    fn constructor_sort(
        &mut self,
        wire: WireSortReference,
    ) -> Result<HostSortReference, Self::Error> {
        self.sort(wire)
    }

    fn constructor_field_sort(
        &mut self,
        wire: WireTypeReference,
    ) -> Result<HostTypeReference, Self::Error> {
        self.nominal(wire)
    }
}

#[cfg(test)]
mod tests {
    use super::{__KrsSlots, __KrsTargetSlot, __krs_host_payload, Decoder};
    use krs_ir::wire::{
        ItemSlot, TargetSlot, TypeSlot, WireApplicationReference, WireConstructorDescriptor,
        WireConstructorFieldDescriptor, WireContextAliasReference, WireGrammarDescriptor,
        WireHeadRule, WirePayload, WireProduction, WireProductionAttribute, WireProductionItem,
        WireProductionOwner, WireSortReference, WireStructuredRule, WireTerm, WireTypeReference,
    };
    use krs_ir::{
        DescriptorAssociativitySentence, DescriptorGroupReference, DescriptorLiteral,
        DescriptorPrecedenceChain, GroupAssociativity, HostConstructorDescriptor,
        HostConstructorFieldDescriptor, HostContextAliasReference, HostDescriptorPayload,
        HostGrammarDescriptor, HostHeadRule, HostItemId, HostPackageKey, HostProduction,
        HostProductionAttribute, HostProductionItem, HostProductionOwner, HostSortReference,
        HostStructuredRuleDescriptor, HostTerm, HostTypeKey, HostTypeReference, ItemKind,
        ProductionGroupId, ProtocolHeadRuleResult, ProvenanceKey, ProvenanceRole, SentenceKind,
        StrictnessKind,
    };
    use std::any::TypeId;

    fn key(role: ProvenanceRole) -> ProvenanceKey {
        ProvenanceKey::new(role, 0)
    }

    fn type_id() -> TypeId {
        TypeId::of::<u64>()
    }

    fn marker_id() -> TypeId {
        TypeId::of::<u32>()
    }

    #[test]
    fn application_slots_reconstruct_diagnostic_paths() {
        let decoder = Decoder {
            slots: __KrsSlots {
                targets: &[
                    __KrsTargetSlot::Nominal(HostTypeKey(type_id)),
                    __KrsTargetSlot::Variant {
                        owner: HostTypeKey(type_id),
                        marker: HostTypeKey(marker_id),
                    },
                ],
                ..__KrsSlots::default()
            },
        };
        let nominal = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: TargetSlot(0),
            authored_path: "int :: add".to_owned(),
        });
        assert_eq!(nominal.target.authored_path(), "int :: add");
        let variant = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: TargetSlot(1),
            authored_path: "Op :: Gt".to_owned(),
        });
        assert_eq!(variant.target.authored_path(), "Op :: Gt");
    }

    fn type_slots() -> __KrsSlots<'static> {
        __KrsSlots {
            types: &[HostTypeKey(type_id)],
            ..__KrsSlots::default()
        }
    }

    fn wire_sort() -> WireSortReference {
        WireSortReference {
            key: key(ProvenanceRole::SortDeclaration),
            target: WireTypeReference {
                slot: TypeSlot(0),
                authored_path: "u64".to_owned(),
            },
        }
    }

    fn host_sort() -> HostSortReference {
        HostSortReference {
            key: key(ProvenanceRole::SortDeclaration),
            target: HostTypeReference {
                key: HostTypeKey(type_id),
                authored_path: "u64".to_owned(),
            },
        }
    }

    fn wire_term() -> WireTerm {
        WireTerm::Literal {
            key: key(ProvenanceRole::TermLiteral),
            literal: DescriptorLiteral::Int("42".to_owned()),
        }
    }

    fn host_term() -> HostTerm {
        HostTerm::Literal {
            key: key(ProvenanceRole::TermLiteral),
            literal: DescriptorLiteral::Int("42".to_owned()),
        }
    }

    fn decode(wire: &WirePayload, slots: __KrsSlots<'_>) -> HostDescriptorPayload {
        let encoded = serde_json::to_string(&wire).unwrap();
        let parsed: WirePayload = krs_ir::json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&parsed).unwrap(), encoded);
        __krs_host_payload(&encoded, slots)
    }

    #[test]
    fn constructor_wire_matches_code_built_payload() {
        let wire = WirePayload::Constructor(WireConstructorDescriptor {
            sort: wire_sort(),
            fields: vec![WireConstructorFieldDescriptor {
                name: "value".to_owned(),
                sort: WireTypeReference {
                    slot: TypeSlot(0),
                    authored_path: "u64".to_owned(),
                },
            }],
        });
        let actual = decode(&wire, type_slots());
        let expected = HostDescriptorPayload::Constructor(HostConstructorDescriptor {
            sort: host_sort(),
            fields: vec![HostConstructorFieldDescriptor {
                name: "value".to_owned(),
                sort: HostTypeReference {
                    key: HostTypeKey(type_id),
                    authored_path: "u64".to_owned(),
                },
            }],
        });
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_associativity_wire_matches_code_built_payload() {
        let sentence = DescriptorAssociativitySentence {
            key: key(ProvenanceRole::AssociativitySentence),
            associativity: GroupAssociativity::Left,
            groups: vec![DescriptorGroupReference {
                key: key(ProvenanceRole::AssociativityGroupReference),
                group: ProductionGroupId::new("arith").unwrap(),
            }],
        };
        let actual = decode(
            &WirePayload::Grammar(Box::new(WireGrammarDescriptor::Associativity {
                key: key(ProvenanceRole::AssociativityDeclaration),
                sentences: vec![sentence.clone()],
            })),
            __KrsSlots::default(),
        );
        let expected =
            HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Associativity {
                key: key(ProvenanceRole::AssociativityDeclaration),
                sentences: vec![sentence],
            }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_production_wire_matches_code_built_payload() {
        let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
            WireProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: WireProductionOwner::TokenSort { sort: wire_sort() },
                result_sort: wire_sort(),
                items: vec![WireProductionItem::Terminal {
                    key: key(ProvenanceRole::ConstructorSyntax),
                    text: "+".to_owned(),
                }],
                attributes: vec![WireProductionAttribute::Function {
                    key: key(ProvenanceRole::FunctionDeclaration),
                }],
            },
        )));
        let actual = decode(&wire, type_slots());
        let expected = HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Production(
            HostProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: HostProductionOwner::TokenSort { sort: host_sort() },
                result_sort: host_sort(),
                items: vec![HostProductionItem::Terminal {
                    key: key(ProvenanceRole::ConstructorSyntax),
                    text: "+".to_owned(),
                }],
                attributes: vec![HostProductionAttribute::Function {
                    key: key(ProvenanceRole::FunctionDeclaration),
                }],
            },
        )));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_ordering_and_subsort_wire_match_code_built_payloads() {
        let chain = DescriptorPrecedenceChain {
            key: key(ProvenanceRole::PrecedenceChain),
            groups: krs_ir::AtLeastTwo::new(
                DescriptorGroupReference {
                    key: key(ProvenanceRole::PrecedenceGroupReference),
                    group: ProductionGroupId::new("arith").unwrap(),
                },
                DescriptorGroupReference {
                    key: krs_ir::ProvenanceKey::new(ProvenanceRole::PrecedenceGroupReference, 1),
                    group: ProductionGroupId::new("atom").unwrap(),
                },
                Vec::new(),
            ),
        };
        let actual = decode(
            &WirePayload::Grammar(Box::new(WireGrammarDescriptor::Precedence {
                key: key(ProvenanceRole::PrecedenceDeclaration),
                chains: vec![chain.clone()],
            })),
            __KrsSlots::default(),
        );
        let expected =
            HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Precedence {
                key: key(ProvenanceRole::PrecedenceDeclaration),
                chains: vec![chain],
            }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));

        let actual = decode(
            &WirePayload::Grammar(Box::new(WireGrammarDescriptor::Subsort {
                key: key(ProvenanceRole::SubsortDeclaration),
                subsort: wire_sort(),
                supersort: wire_sort(),
            })),
            type_slots(),
        );
        let expected = HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Subsort {
            key: key(ProvenanceRole::SubsortDeclaration),
            subsort: host_sort(),
            supersort: host_sort(),
        }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn grammar_strictness_item_slot_matches_code_built_payload() {
        let package =
            HostPackageKey::new("semantics", "0.1.0", std::env::current_dir().unwrap()).unwrap();
        let alias =
            HostItemId::new(package, ["semantics"], "eval", ItemKind::ContextAlias, "").unwrap();
        let wire = WirePayload::Grammar(Box::new(WireGrammarDescriptor::Production(
            WireProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: WireProductionOwner::TokenSort { sort: wire_sort() },
                result_sort: wire_sort(),
                items: vec![],
                attributes: vec![WireProductionAttribute::Strictness {
                    key: key(ProvenanceRole::StrictnessDeclaration),
                    kind: StrictnessKind::Strict,
                    using: Some(WireContextAliasReference {
                        key: key(ProvenanceRole::AliasProduction),
                        slot: ItemSlot(0),
                    }),
                    fields: vec![],
                    result_sort: Box::new(wire_sort()),
                }],
            },
        )));
        let actual = decode(
            &wire,
            __KrsSlots {
                types: &[HostTypeKey(type_id)],
                items: std::slice::from_ref(&alias),
                targets: &[],
            },
        );
        let expected = HostDescriptorPayload::Grammar(Box::new(HostGrammarDescriptor::Production(
            HostProduction {
                key: key(ProvenanceRole::ConstructorDeclaration),
                template_key: None,
                owner: HostProductionOwner::TokenSort { sort: host_sort() },
                result_sort: host_sort(),
                items: vec![],
                attributes: vec![HostProductionAttribute::Strictness {
                    key: key(ProvenanceRole::StrictnessDeclaration),
                    kind: StrictnessKind::Strict,
                    using: Some(HostContextAliasReference {
                        key: key(ProvenanceRole::AliasProduction),
                        alias,
                    }),
                    fields: vec![],
                    result_sort: Box::new(host_sort()),
                }],
            },
        )));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn structured_wire_matches_code_built_payload() {
        let wire = WirePayload::StructuredRule(Box::new(WireStructuredRule {
            sentence_kind: SentenceKind::Equation,
            label: None,
            requires: None,
            priority: None,
            nondet: None,
            simplification: None,
            pattern_key: key(ProvenanceRole::RulePattern),
            result_key: key(ProvenanceRole::RuleResult),
            subject_sort: wire_sort(),
            result_sort: wire_sort(),
            bindings: vec![],
            subject: wire_term(),
            result: wire_term(),
        }));
        let encoded = serde_json::to_string(&wire).unwrap();
        assert!(encoded.contains("\"slot\":0,\"authored_path\":\"u64\""));
        let decoded: WirePayload = krs_ir::json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&decoded).unwrap(), encoded);
        let actual = __krs_host_payload(&encoded, type_slots());
        let expected =
            HostDescriptorPayload::StructuredRule(Box::new(HostStructuredRuleDescriptor {
                sentence_kind: SentenceKind::Equation,
                label: None,
                requires: None,
                priority: None,
                nondet: None,
                simplification: None,
                pattern_key: key(ProvenanceRole::RulePattern),
                result_key: key(ProvenanceRole::RuleResult),
                subject_sort: host_sort(),
                result_sort: host_sort(),
                bindings: vec![],
                subject: host_term(),
                result: host_term(),
            }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    #[test]
    fn head_wire_matches_code_built_payload() {
        let wire = WirePayload::HeadRule(Box::new(WireHeadRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            pattern_key: key(ProvenanceRole::RulePattern),
            result_key: key(ProvenanceRole::RuleResult),
            head_sort: Some(wire_sort()),
            configuration: None,
            computation_cell_name: None,
            bindings: vec![],
            subject: wire_term(),
            result: ProtocolHeadRuleResult::Erase,
            requires: None,
            extras: vec![],
        }));
        let encoded = serde_json::to_string(&wire).unwrap();
        let decoded: WirePayload = krs_ir::json::from_slice(encoded.as_bytes()).unwrap();
        assert_eq!(serde_json::to_string(&decoded).unwrap(), encoded);
        let actual = __krs_host_payload(&encoded, type_slots());
        let expected = HostDescriptorPayload::HeadRule(Box::new(HostHeadRule {
            sentence_kind: SentenceKind::Transition,
            label: None,
            priority: None,
            nondet: None,
            pattern_key: key(ProvenanceRole::RulePattern),
            result_key: key(ProvenanceRole::RuleResult),
            head_sort: Some(host_sort()),
            configuration: None,
            computation_cell_name: None,
            bindings: vec![],
            subject: host_term(),
            result: ProtocolHeadRuleResult::Erase,
            requires: None,
            extras: vec![],
        }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
    }

    fn wire_nominal(slot: usize, path: &str) -> WireTypeReference {
        WireTypeReference {
            slot: TypeSlot(slot),
            authored_path: path.to_owned(),
        }
    }

    fn host_nominal(path: &str) -> HostTypeReference {
        HostTypeReference {
            key: HostTypeKey(type_id),
            authored_path: path.to_owned(),
        }
    }

    fn wire_cell() -> krs_ir::wire::WireCellReference {
        krs_ir::wire::WireCellReference {
            key: key(ProvenanceRole::ConfigurationField),
            cell: krs_ir::wire::WireCellIdentity {
                owner: TypeSlot(0),
                field: TypeSlot(1),
            },
        }
    }

    fn host_cell() -> krs_ir::HostCellReference {
        krs_ir::HostCellReference {
            key: key(ProvenanceRole::ConfigurationField),
            cell: krs_ir::HostCellIdentity {
                owner: HostTypeKey(type_id),
                field: HostTypeKey(marker_id),
            },
        }
    }

    fn cell_slots() -> __KrsSlots<'static> {
        __KrsSlots {
            types: &[HostTypeKey(type_id), HostTypeKey(marker_id)],
            ..__KrsSlots::default()
        }
    }

    fn wire_declaration() -> krs_ir::wire::WireCellDeclaration {
        use krs_ir::{
            CellWrapper, ProtocolCellContent, ProtocolCellDeclaration, ProtocolCellField,
        };
        ProtocolCellDeclaration {
            key: key(ProvenanceRole::ConfigurationDeclaration),
            fields: vec![
                ProtocolCellField {
                    reference: wire_cell(),
                    rust_field: "value".to_owned(),
                    emitted_name: None,
                    color: None,
                    multiplicity: None,
                    cell_type: None,
                    content: ProtocolCellContent::Leaf {
                        wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper),
                        wrapper: CellWrapper::Cell,
                        sort: wire_sort(),
                        arguments: vec![wire_sort()],
                    },
                },
                ProtocolCellField {
                    reference: wire_cell(),
                    rust_field: "nested".to_owned(),
                    emitted_name: None,
                    color: None,
                    multiplicity: None,
                    cell_type: None,
                    content: ProtocolCellContent::Nested {
                        declaration: krs_ir::wire::WireCellDeclarationReference {
                            key: key(ProvenanceRole::ConfigurationField),
                            declaration: wire_nominal(0, "Nested"),
                        },
                    },
                },
            ],
        }
    }

    fn host_declaration() -> krs_ir::HostCellDeclaration {
        use krs_ir::{
            CellWrapper, ProtocolCellContent, ProtocolCellDeclaration, ProtocolCellField,
        };
        ProtocolCellDeclaration {
            key: key(ProvenanceRole::ConfigurationDeclaration),
            fields: vec![
                ProtocolCellField {
                    reference: host_cell(),
                    rust_field: "value".to_owned(),
                    emitted_name: None,
                    color: None,
                    multiplicity: None,
                    cell_type: None,
                    content: ProtocolCellContent::Leaf {
                        wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper),
                        wrapper: CellWrapper::Cell,
                        sort: host_sort(),
                        arguments: vec![host_sort()],
                    },
                },
                ProtocolCellField {
                    reference: host_cell(),
                    rust_field: "nested".to_owned(),
                    emitted_name: None,
                    color: None,
                    multiplicity: None,
                    cell_type: None,
                    content: ProtocolCellContent::Nested {
                        declaration: krs_ir::HostCellDeclarationReference {
                            key: key(ProvenanceRole::ConfigurationField),
                            declaration: host_nominal("Nested"),
                        },
                    },
                },
            ],
        }
    }

    #[test]
    fn sort_wire_matches_code_built_payload_and_resolves_parent_identity() {
        let actual = decode(
            &WirePayload::Sort(krs_ir::wire::WireSortDescriptor {
                parents: vec![wire_nominal(0, "u64")],
            }),
            type_slots(),
        );
        let expected = HostDescriptorPayload::Sort(krs_ir::HostSortDescriptor {
            parents: vec![host_nominal("u64")],
        });
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        let HostDescriptorPayload::Sort(sort) = actual else {
            panic!("wrong payload kind")
        };
        assert_eq!(sort.parents[0].key.resolve(), type_id());
    }

    #[test]
    fn cell_wire_matches_code_built_payload_and_resolves_exact_owner_marker_pair() {
        let actual = decode(
            &WirePayload::Cell(Box::new(wire_declaration())),
            cell_slots(),
        );
        let expected = HostDescriptorPayload::Cell(Box::new(host_declaration()));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        let HostDescriptorPayload::Cell(declaration) = actual else {
            panic!("wrong payload kind")
        };
        assert_eq!(
            declaration.fields[0].reference.cell.resolve(),
            (type_id(), marker_id())
        );
        let krs_ir::ProtocolCellContent::Nested { declaration } = &declaration.fields[1].content
        else {
            panic!("wrong cell content")
        };
        assert_eq!(declaration.declaration.key.resolve(), type_id());
    }

    fn wire_initializer() -> krs_ir::wire::WireConfigurationInitializer {
        use krs_ir::{
            CellWrapper, ProtocolConfigurationInitializer, ProtocolConfigurationVariable,
            ProtocolInitializerCell, ProtocolInitializerCellContent, ProtocolInitializerStateTerm,
            ProtocolInitializerTerm,
        };
        ProtocolConfigurationInitializer {
            key: key(ProvenanceRole::InitializerDeclaration),
            owner_key: key(ProvenanceRole::InitializerResultType),
            owner: wire_nominal(0, "Configuration"),
            body_key: key(ProvenanceRole::InitializerBody),
            variables: vec![ProtocolConfigurationVariable {
                binding_key: key(ProvenanceRole::ConfigurationVariable),
                binding: "input".to_owned(),
                external_name_key: key(ProvenanceRole::ConfigurationVariable),
                external_name: "INPUT".to_owned(),
                sort: wire_sort(),
                main_key: None,
            }],
            cells: vec![ProtocolInitializerCell {
                key: key(ProvenanceRole::InitializerCell),
                field: wire_cell(),
                content: ProtocolInitializerCellContent::Nested {
                    declaration: krs_ir::wire::WireCellDeclarationReference {
                        key: key(ProvenanceRole::InitializerCell),
                        declaration: wire_nominal(0, "Nested"),
                    },
                    children: vec![ProtocolInitializerCell {
                        key: key(ProvenanceRole::InitializerCell),
                        field: wire_cell(),
                        content: ProtocolInitializerCellContent::Leaf {
                            constructor_key: key(ProvenanceRole::InitializerCell),
                            wrapper: CellWrapper::Cell,
                            value: ProtocolInitializerStateTerm::Term(ProtocolInitializerTerm {
                                key: key(ProvenanceRole::InitializerCell),
                                term: wire_term(),
                            }),
                        },
                    }],
                },
            }],
        }
    }

    fn host_initializer() -> krs_ir::HostConfigurationInitializer {
        use krs_ir::{
            CellWrapper, ProtocolConfigurationInitializer, ProtocolConfigurationVariable,
            ProtocolInitializerCell, ProtocolInitializerCellContent, ProtocolInitializerStateTerm,
            ProtocolInitializerTerm,
        };
        ProtocolConfigurationInitializer {
            key: key(ProvenanceRole::InitializerDeclaration),
            owner_key: key(ProvenanceRole::InitializerResultType),
            owner: HostTypeKey(type_id),
            body_key: key(ProvenanceRole::InitializerBody),
            variables: vec![ProtocolConfigurationVariable {
                binding_key: key(ProvenanceRole::ConfigurationVariable),
                binding: "input".to_owned(),
                external_name_key: key(ProvenanceRole::ConfigurationVariable),
                external_name: "INPUT".to_owned(),
                sort: host_sort(),
                main_key: None,
            }],
            cells: vec![ProtocolInitializerCell {
                key: key(ProvenanceRole::InitializerCell),
                field: host_cell(),
                content: ProtocolInitializerCellContent::Nested {
                    declaration: krs_ir::HostCellDeclarationReference {
                        key: key(ProvenanceRole::InitializerCell),
                        declaration: host_nominal("Nested"),
                    },
                    children: vec![ProtocolInitializerCell {
                        key: key(ProvenanceRole::InitializerCell),
                        field: host_cell(),
                        content: ProtocolInitializerCellContent::Leaf {
                            constructor_key: key(ProvenanceRole::InitializerCell),
                            wrapper: CellWrapper::Cell,
                            value: ProtocolInitializerStateTerm::Term(ProtocolInitializerTerm {
                                key: key(ProvenanceRole::InitializerCell),
                                term: host_term(),
                            }),
                        },
                    }],
                },
            }],
        }
    }

    #[test]
    fn fixed_configuration_wire_and_separately_indexed_initializer_match_code_built_payload() {
        let root = krs_ir::DescriptorConfigurationRoot::GeneratedTop;
        let declaration = wire_declaration();
        let mut initializer = wire_initializer();
        let actual = decode(
            &WirePayload::FixedConfiguration(Box::new(krs_ir::wire::WireFixedConfiguration {
                root: root.clone(),
                declaration: declaration.clone(),
                initializer: initializer.clone(),
            })),
            cell_slots(),
        );
        let expected =
            HostDescriptorPayload::FixedConfiguration(Box::new(krs_ir::HostFixedConfiguration {
                root: root.clone(),
                declaration: host_declaration(),
                initializer: host_initializer(),
            }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        let HostDescriptorPayload::FixedConfiguration(configuration) = &actual else {
            panic!("wrong payload kind")
        };
        assert_eq!(configuration.initializer.owner.resolve(), type_id());
        assert_eq!(
            configuration.initializer.cells[0].field.cell.resolve(),
            (type_id(), marker_id())
        );
        initializer.owner.slot = TypeSlot(1);
        initializer.variables[0].sort.target.slot = TypeSlot(1);
        initializer.cells[0].field.cell = krs_ir::wire::WireCellIdentity {
            owner: TypeSlot(1),
            field: TypeSlot(0),
        };
        let krs_ir::ProtocolInitializerCellContent::Nested {
            declaration: nested,
            children,
        } = &mut initializer.cells[0].content
        else {
            panic!("wrong initializer content")
        };
        nested.declaration.slot = TypeSlot(1);
        children[0].field.cell = krs_ir::wire::WireCellIdentity {
            owner: TypeSlot(1),
            field: TypeSlot(0),
        };
        let joined = cell_slots().__krs_fixed_configuration(
            &serde_json::to_string(&(root, declaration)).unwrap(),
            &serde_json::to_string(&initializer).unwrap(),
            __KrsSlots {
                types: &[HostTypeKey(marker_id), HostTypeKey(type_id)],
                ..__KrsSlots::default()
            },
        );
        assert_eq!(format!("{joined:?}"), format!("{expected:?}"));
        let HostDescriptorPayload::FixedConfiguration(configuration) = joined else {
            panic!("wrong payload kind")
        };
        assert_eq!(configuration.initializer.owner.resolve(), type_id());
        assert_eq!(
            configuration.initializer.variables[0]
                .sort
                .target
                .key
                .resolve(),
            type_id()
        );
        assert_eq!(
            configuration.initializer.cells[0].field.cell.resolve(),
            (type_id(), marker_id())
        );
    }

    fn wire_cells() -> krs_ir::wire::WireRuleCells {
        krs_ir::ProtocolRuleCells {
            key: key(ProvenanceRole::RulePattern),
            remainder: krs_ir::ProtocolRuleFrame::Exact,
            cells: vec![krs_ir::ProtocolRuleCell {
                field: wire_cell(),
                wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper),
                wrapper: krs_ir::CellWrapper::Cell,
                value: krs_ir::ProtocolRuleStateTerm::Term(wire_term()),
            }],
        }
    }

    fn host_cells() -> krs_ir::HostRuleCells {
        krs_ir::ProtocolRuleCells {
            key: key(ProvenanceRole::RulePattern),
            remainder: krs_ir::ProtocolRuleFrame::Exact,
            cells: vec![krs_ir::ProtocolRuleCell {
                field: host_cell(),
                wrapper_key: key(ProvenanceRole::ConfigurationCellWrapper),
                wrapper: krs_ir::CellWrapper::Cell,
                value: krs_ir::ProtocolRuleStateTerm::Term(host_term()),
            }],
        }
    }

    fn wire_configuration() -> krs_ir::wire::WireConfigurationReference {
        krs_ir::wire::WireConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration: wire_nominal(0, "Configuration"),
        }
    }

    fn host_configuration() -> krs_ir::HostConfigurationReference {
        krs_ir::HostConfigurationReference {
            key: key(ProvenanceRole::RuleType),
            configuration: host_nominal("Configuration"),
        }
    }

    #[test]
    fn configuration_rule_and_claim_wire_match_code_built_payloads() {
        for sentence_kind in [SentenceKind::Transition, SentenceKind::Claim] {
            let claim = (sentence_kind == SentenceKind::Claim).then(|| krs_ir::wire::WireClaim {
                declaration_key: key(ProvenanceRole::ClaimDeclaration),
                modality_key: key(ProvenanceRole::ClaimDeclaration),
                modality: krs_ir::ClaimModality::OnePath,
                circularity_key: None,
                universals: vec![krs_ir::wire::WireClaimBinder {
                    declaration_key: key(ProvenanceRole::ClaimDeclaration),
                    name_key: key(ProvenanceRole::ClaimDeclaration),
                    name: "value".to_owned(),
                    sort: wire_sort(),
                }],
                existentials: vec![],
                ensures: None,
                or_bool_keys: vec![],
            });
            let host_claim = (sentence_kind == SentenceKind::Claim).then(|| krs_ir::HostClaim {
                declaration_key: key(ProvenanceRole::ClaimDeclaration),
                modality_key: key(ProvenanceRole::ClaimDeclaration),
                modality: krs_ir::ClaimModality::OnePath,
                circularity_key: None,
                universals: vec![krs_ir::HostClaimBinder {
                    declaration_key: key(ProvenanceRole::ClaimDeclaration),
                    name_key: key(ProvenanceRole::ClaimDeclaration),
                    name: "value".to_owned(),
                    sort: host_sort(),
                }],
                existentials: vec![],
                ensures: None,
                or_bool_keys: vec![],
            });
            let actual = decode(
                &WirePayload::ConfigurationRule(Box::new(krs_ir::wire::WireConfigurationRule {
                    sentence_kind: sentence_kind.try_into().unwrap(),
                    label: None,
                    priority: None,
                    nondet: None,
                    requires: None,
                    claim,
                    pattern_key: key(ProvenanceRole::RulePattern),
                    result_key: key(ProvenanceRole::RuleResult),
                    subject_configuration: wire_configuration(),
                    result_configuration: wire_configuration(),
                    bindings: vec![],
                    subject: wire_cells(),
                    result: wire_cells(),
                })),
                cell_slots(),
            );
            let expected =
                HostDescriptorPayload::ConfigurationRule(Box::new(krs_ir::HostConfigurationRule {
                    sentence_kind: sentence_kind.try_into().unwrap(),
                    label: None,
                    priority: None,
                    nondet: None,
                    requires: None,
                    claim: host_claim,
                    pattern_key: key(ProvenanceRole::RulePattern),
                    result_key: key(ProvenanceRole::RuleResult),
                    subject_configuration: host_configuration(),
                    result_configuration: host_configuration(),
                    bindings: vec![],
                    subject: host_cells(),
                    result: host_cells(),
                }));
            assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
            let HostDescriptorPayload::ConfigurationRule(rule) = actual else {
                panic!("wrong payload kind")
            };
            assert_eq!(
                rule.subject_configuration.configuration.key.resolve(),
                type_id()
            );
            assert_eq!(
                rule.subject.cells[0].field.cell.resolve(),
                (type_id(), marker_id())
            );
        }
    }

    #[test]
    fn context_alias_wire_matches_code_built_payload() {
        let actual = decode(
            &WirePayload::ContextAlias(Box::new(krs_ir::wire::WireContextAlias {
                declaration_key: key(ProvenanceRole::ContextAliasDeclaration),
                name_key: key(ProvenanceRole::ContextAliasName),
                name: "evaluation".to_owned(),
                here_key: key(ProvenanceRole::ContextAliasHere),
                here: "here".to_owned(),
                pattern_key: key(ProvenanceRole::RulePattern),
                configuration: wire_configuration(),
                bindings: vec![krs_ir::ProtocolContextAliasBinding {
                    name: "other".to_owned(),
                    kind: krs_ir::ProtocolContextAliasBindingKind::Term { sort: wire_sort() },
                }],
                pattern: wire_cells(),
            })),
            cell_slots(),
        );
        let expected = HostDescriptorPayload::ContextAlias(Box::new(krs_ir::HostContextAlias {
            declaration_key: key(ProvenanceRole::ContextAliasDeclaration),
            name_key: key(ProvenanceRole::ContextAliasName),
            name: "evaluation".to_owned(),
            here_key: key(ProvenanceRole::ContextAliasHere),
            here: "here".to_owned(),
            pattern_key: key(ProvenanceRole::RulePattern),
            configuration: host_configuration(),
            bindings: vec![krs_ir::ProtocolContextAliasBinding {
                name: "other".to_owned(),
                kind: krs_ir::ProtocolContextAliasBindingKind::Term { sort: host_sort() },
            }],
            pattern: host_cells(),
        }));
        assert_eq!(format!("{actual:?}"), format!("{expected:?}"));
        let HostDescriptorPayload::ContextAlias(alias) = actual else {
            panic!("wrong payload kind")
        };
        assert_eq!(alias.configuration.configuration.key.resolve(), type_id());
        assert_eq!(
            alias.pattern.cells[0].field.cell.resolve(),
            (type_id(), marker_id())
        );
    }

    #[test]
    #[should_panic(expected = "KRS generated rule wire has an invalid type slot 0")]
    fn out_of_range_type_slot_panics() {
        let wire = WirePayload::Constructor(WireConstructorDescriptor {
            sort: wire_sort(),
            fields: vec![],
        });
        let _ = decode(&wire, __KrsSlots::default());
    }

    #[test]
    #[should_panic(expected = "KRS generated rule wire has an invalid target slot 2")]
    fn out_of_range_target_slot_panics() {
        let decoder = Decoder {
            slots: __KrsSlots::default(),
        };
        let _ = decoder.target(WireApplicationReference {
            key: key(ProvenanceRole::TermApplicationHead),
            target: TargetSlot(2),
            authored_path: "Op".to_owned(),
        });
    }

    #[test]
    #[should_panic(expected = "KRS generated wire has an invalid item slot 3")]
    fn out_of_range_item_slot_panics() {
        let mut decoder = Decoder {
            slots: __KrsSlots::default(),
        };
        let _ =
            krs_ir::RefMap::<krs_ir::WireStage, krs_ir::HostStage>::item(&mut decoder, ItemSlot(3));
    }

    #[test]
    #[should_panic(expected = "KRS generated rule wire is malformed")]
    fn malformed_wire_panics() {
        let _ = __krs_host_payload("{", __KrsSlots::default());
    }
}
